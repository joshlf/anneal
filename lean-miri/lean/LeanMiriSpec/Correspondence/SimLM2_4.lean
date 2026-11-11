/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.UnionLM2_4

/-!
# Lockstep Simulation for Unions and `Subslice` (`LM-2.4`)

The theorems here relate Anneal's `MirSemantics` to `lean-miri` running the
`LM-2.4` hooks `annealStepHooksLM2_4`. On bodies without union or `Subslice`
assignments those hooks take exactly the steps of `annealStepHooksLM2_2`
(`step_LM2_4_eq_of_bodyFree`).

The agreeing fragment covers unions of primitive scalar fields that hold active
field `f`'s (`f < n`) value: Anneal's
`Value.aggregate 0 (unionSlotFields n f (.scalar sc))` corresponds to an
allocation whose bytes `[0, k)` hold `sc` and are initialized while its bytes
`[k, S)` are not (`UnionMemRel`, `StateRelLM2_4`). Within it:

* `step_union_aggregate_simulation` and
  `evalRvalue_union_aggregate_activeField_simulation`: `_u = U { field_f: op }`
  (`activeField = some f` for any `f < n`) into an uninitialized union stores
  `.scalar sc` at slot `f` and `.unit` at all sibling slots in Anneal while
  initializing `[0, k)` in `lean-miri` (the write half of `I-11`);
* `step_union_field_read_simulation`,
  `step_union_type_punning_read_simulation`, and
  `union_uninit_bytes_read_ub_simulation`: reading active field `f` returns
  `sc`, reading a cross-field `j ≠ f` of width `w ≤ sc.sizeBytes` decodes the
  low `w` little-endian bytes in lockstep, and reading a wider field `j ≠ f`
  (`sc.sizeBytes < w ≤ S`) whose bytes include an uninitialized byte is
  undefined behavior in both machines;
* `union_field_write_read_same_field_simulation`: the aggregate and the read of
  the same field, composed;
* `union_whole_copy_initMask_preservation_simulation` and
  `union_whole_move_initMask_preservation_simulation`: `_w = copy _u` (or
  `move _u`) copies the bytes and the initialization mask with the vendored
  `Allocation.copy`, without reporting undefined behavior, leaving the bytes
  `[k, S)` of the copy uninitialized (the copy half of `I-11`);
* `step_union_whole_copy_or_move_overwrite_simulation` and
  `step_union_aggregate_overwrite_simulation`: whole-union copies/moves and
  same-or-wider union aggregates into already-allocated or dead destinations;
* `step_union_field_write_simulation`,
  `step_union_field_write_uninit_simulation`, and
  `step_union_nonzero_field_write_simulation`: `_u.j = op` writes into an
  uninitialized union (`uninitFieldWriteShell?` + `forceAllocation`) and
  rewrites same-or-wider fields in place on an initialized union. Narrower
  projected field writes (`w_j < sc_old.sizeBytes`) leave the fragment:
  `step_union_narrower_field_write_correspondence` shows both machines retain
  the high bytes `[w_j, sc_old.sizeBytes)` (Anneal's raw-byte overlay via
  `finalizeUnionFieldsWithRawOverlayOpt`, `lean-miri`'s spliced `UnionMemRel`
  via `unionSpliceLowScalar`), but `StateRelLM2_4` is not re-established for the
  overlay-carrying union value;
* `step_repeat_union_field_simulation`: `_arr = [copy u.j; count]` (or `move`)
  for union field operands (`writeRepeat` on `annealAggregateHooksLM2_4`);
* `step_storageLive_LM2_4_simulation` and `step_storageDead_LM2_4_simulation`:
  `StorageLive` and `StorageDead` on `StateRelLM2_4`, freeing any backing union
  or array stack allocation;
* `evalProjection_subslice_simulation`,
  `evalProjection_nested_subslice_simulation`, and
  `step_subslice_elem_write_simulation`: single and nested `Subslice`
  projections of arrays and projected element writes `a[i..j][k] = c` agree in
  value and in place, and out-of-bounds ones are undefined behavior in both
  machines; `evalSubsliceOperand_simulation`, `step_subslice_assign_simulation`,
  and `step_subslice_assign_overwrite_simulation` lift this to `copy a[i..j]`
  and `move a[i..j]` into uninitialized, dead, and already-allocated array
  locals.

Outside the fragment, the remaining boundary theorems characterize irreducible
differences against vendored `lean-miri/vendor` or Anneal's value-tree model:
`Subslice` bounds that vendored `prepareSubslice` rejects with `.invalidProgram`
or accepts without checking (`evalProjection_subslice_inverted_divergence`,
`evalProjection_subslice_fromEndFalse_oob_divergence`), `[T; 0]` indirect
uninitialized mask representation (`evalSubsliceOperand_zero_uninit_indirect_characterization`),
narrower union aggregate overwrites where pure Rvalue replacement drops high
bytes `[k₂, k₁)` (`step_union_aggregate_smaller_overwrite_divergence`),
self-copy `_u = copy _u` on a nonzero-sized memory-backed union
(`step_union_self_copy_overlap_divergence`), and whole-union copy of an
indirect uninitialized allocation (`step_union_copy_indirect_uninit_divergence`).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Relation Plumbing -/

namespace FrameRelLM2_4

theorem lookup_local
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4 body mach af mf) {i : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls i = some decl) :
    ∃ (slot : LocalSlot) (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
      (_ : i < af.locals.length) (hlt_mf : i < mf.locals.size),
      get? af.locals i = some slot ∧
      mf.locals[i]? = some mls ∧
      mf.locals[i]'hlt_mf = mls ∧
      UnionLocalRel mach decl body.layouts slot mls := by
  rw [get?_eq_getElem?] at hdecl
  obtain ⟨hlt_d, _⟩ := List.getElem?_eq_some_iff.mp hdecl
  have hlt_af : i < af.locals.length := by rw [hrel.af_locals_len]; exact hlt_d
  have hlt_mf : i < mf.locals.size := by rw [hrel.mf_locals_size]; exact hlt_d
  have hslot : get? af.locals i = some (af.locals[i]'hlt_af) := by
    rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt_af]
  have hmls : mf.locals[i]? = some (mf.locals[i]'hlt_mf) :=
    Array.getElem?_eq_getElem hlt_mf
  have hdecl' : get? body.localDecls i = some decl := hdecl
  exact ⟨af.locals[i]'hlt_af, mf.locals[i]'hlt_mf, hlt_af, hlt_mf, hslot, hmls, rfl,
    hrel.locals_rel i decl _ _ hdecl' hslot hmls⟩

theorem update_local
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4 body mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot) (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : UnionLocalRel mach decl body.layouts newSlot
      { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRelLM2_4 body mach
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf } where
  body_eq := hrel.body_eq
  location_eq := hrel.location_eq
  af_locals_len := by rw [List.length_set, hrel.af_locals_len]
  mf_locals_size := by rw [Array.size_set, hrel.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    have hlt_af : idx < af.locals.length := by
      rw [hrel.af_locals_len, ← hrel.mf_locals_size]; exact hlt_mf
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i hmls_i
      have hdecl_eq : decl_i = decl := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
      subst hdecl_eq hslot_i hmls_i
      exact hnew
    · simp only [h_eq, ↓reduceIte] at hslot_i hmls_i
      exact hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i

end FrameRelLM2_4

theorem UnionLocalRel.cache_layout
    {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot} {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : UnionLocalRel mach decl layouts slot mls) :
    UnionLocalRel mach decl layouts slot
      { mls with layout := some (translateTy decl.ty layouts) } := by
  cases h with
  | base _ _ hl => exact .base _ _ hl.cache_layout
  | union S n f f0Ty sc mp _ _ hwt hfields hf hmem =>
    exact .union S n f f0Ty sc mp _ (fun l hl => (Option.some.inj hl).symm) hwt hfields hf hmem

theorem FrameRelLM2_4.cache_local_layout
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4 body mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    (hlt_mf : idx < mf.locals.size) :
    FrameRelLM2_4 body mach af
      (cacheFrameLocalLayout mf idx hlt_mf (translateTy decl.ty body.layouts)) where
  body_eq := hrel.body_eq
  location_eq := hrel.location_eq
  af_locals_len := hrel.af_locals_len
  mf_locals_size := by unfold cacheFrameLocalLayout; rw [Array.size_set, hrel.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    unfold cacheFrameLocalLayout at hmls_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, Option.some.injEq] at hmls_i
      rw [hdecl] at hdecl_i
      cases hdecl_i
      cases hmls_i
      have hmls_orig : mf.locals[idx]? = some (mf.locals[idx]'hlt_mf) :=
        Array.getElem?_eq_getElem hlt_mf
      exact (hrel.locals_rel idx decl slot_i _ hdecl hslot_i hmls_orig).cache_layout
    · simp only [h_eq, ↓reduceIte] at hmls_i
      exact hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i

/-- The size of field `0` of a union related by `UnionMemRel`. -/
theorem UnionMemRel.f0_size {mach : AnnealMachine} {uTy : Ty} {layouts : LayoutTable}
    {S : Nat} {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : UnionMemRel mach uTy layouts S f0Ty sc mp) :
    (translateTy f0Ty layouts).layout.size = translateSizeBytes sc.sizeBytes ∧
      ValidScalarBytes sc.sizeBytes := by
  cases h with
  | mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrel _ himm _ =>
    cases himm with
    | scalar _ _ _ hsz _ _ => exact ⟨hsz, hrel.validBytes⟩

theorem UnionLocalRel.layout_eq
    {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot} {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : UnionLocalRel mach decl layouts slot mls) :
    ∀ l, mls.layout = some l → l = translateTy decl.ty layouts := by
  cases h with
  | base _ _ hl => exact hl.layout_eq
  | union _ _ _ _ _ _ _ hc _ _ _ _ => exact hc

/-! ## 2. Union Field Projections -/

theorem projectionMemoryOffset_zero
    (resolve : Miri.Memory.PointerResolver AnnealProv Unit)
    (lookup : Miri.Memory.LiveAllocationLookup)
    (mp : Miri.Interpreter.MemPlace AnnealProv) :
    Miri.Interpreter.projectionMemoryOffset annealPointerArithmetic resolve lookup
        mp Miri.ABI.Size.ZERO .inbounds .none =
      .ok { mp with ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + 0) },
                    metadata := .none } := by
  unfold Miri.Interpreter.projectionMemoryOffset Miri.Interpreter.MemPlace.offsetWithMeta
    Miri.Interpreter.ptrOffsetInbounds Miri.Memory.checkPtrAccessSigned
    Miri.Memory.checkAndDerefPtr Miri.Memory.Pointer.wrappingSignedOffset
  rw [pointer_wrappingOffset_anneal_eq]
  rfl

/-- Offsetting a thin memory place by zero bytes leaves it unchanged. -/
theorem memPlace_offset_zero_eq (mp : Miri.Interpreter.MemPlace AnnealProv)
    (hmeta : mp.metadata = .none) :
    { mp with ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + 0) },
              metadata := .none } = mp := by
  rcases mp with ⟨⟨⟨off⟩, prov⟩, meta_, mis⟩
  dsimp only at hmeta
  subst hmeta
  simp [Miri.ABI.Size.ofBytes]

/-- Projecting a memory-backed union operand to field `j < n` with a primitive
scalar field type `fty` stays at offset `0` and takes `fty`'s layout. -/
theorem projectField_union
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (layouts : LayoutTable) (mach : AnnealMachine)
    {uLay : Miri.Interpreter.LocalLayout} {n j : Nat}
    (hfields : uLay.layout.fields = .Union n) (hj : j < n)
    {fty : Ty} (hprim : IsPrimScalarTy fty)
    {mp : Miri.Interpreter.MemPlace AnnealProv} (hmeta : mp.metadata = .none) :
    Miri.Interpreter.projectField (annealUnionProjectionCx frame layouts mach (encodeTyId fty))
        ⟨.indirect mp, uLay⟩ j =
      .ok ⟨.indirect mp, translateTy fty layouts⟩ := by
  have hoff : uLay.layout.fields.offset j = .ok Miri.ABI.Size.ZERO := by
    rw [hfields]
    unfold Miri.ABI.FieldsShape.offset Miri.ABI.FieldsShape.count
    have : ¬ j ≥ n := by omega
    simp [this, pure, Except.pure]
  have hsized := hprim.isSized (layouts := layouts)
  have hlay := hprim.layoutOfEncoded (layouts := layouts)
  unfold Miri.Interpreter.projectField
  simp only [bind, Except.bind, hoff, Except.mapError]
  simp only [annealUnionProjectionCx, hfields, hlay, hsized, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, pure, Except.pure]
  unfold Miri.Interpreter.OpTy.offsetWithMeta
  simp only [annealProjectionCx, bind, Except.bind, projectionMemoryOffset_zero,
    memPlace_offset_zero_eq mp hmeta, pure, Except.pure]

/-- `annealEvalUnionField` on a memory-backed union local caches the local's
layout and projects to field `j` at offset `0`. -/
theorem annealEvalUnionField_indirect
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame])
    {u : Nat} {uDecl : LocalDecl} (hlt : u < topFrame.locals.size)
    (hdecl : get? body.localDecls u = some uDecl)
    (hcache : ∀ l, (topFrame.locals[u]'hlt).layout = some l →
      l = translateTy uDecl.ty body.layouts)
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hval : (topFrame.locals[u]'hlt).value = .live (.indirect mp))
    (hmeta : mp.metadata = .none)
    {n j : Nat} (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hj : j < n) {fty : Ty} (hprim : IsPrimScalarTy fty) :
    annealEvalUnionField body.localDecls body.layouts u j (encodeTyId fty) m =
      .ok ⟨.indirect mp, translateTy fty body.layouts⟩
        { m with stack := ⟨#[cacheFrameLocalLayout topFrame u hlt
          (translateTy uDecl.ty body.layouts)]⟩ } := by
  have hres := annealResolveAndCacheLocalLayout_eq (known := none) hframes hlt hdecl hcache
  have hgo : (cacheFrameLocalLayout topFrame u hlt
      (translateTy uDecl.ty body.layouts)).getLocalOperand u = .ok (.indirect mp) := by
    apply frame_getLocalOperand_live
    rw [cacheFrameLocalLayout_getLocal]
    rw [← hval]
  have hproj := projectField_union
    (cacheFrameLocalLayout topFrame u hlt (translateTy uDecl.ty body.layouts))
    body.layouts m.machine hfields hj hprim hmeta
  unfold annealEvalUnionField
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone_some,
    Bool.false_eq_true, ↓reduceIte, hres, hgo, pure, EStateM.pure]
  rw [hproj]
  rfl

/-- The fields shape of a primitive scalar layout. -/
theorem IsPrimScalarTy.fields_primitive {ty : Ty} {layouts : LayoutTable}
    (h : IsPrimScalarTy ty) : (translateTy ty layouts).layout.fields = .Primitive := by
  rcases h with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
    (try cases it) <;> (try cases ut) <;> simp [translateTy, hk] <;> rfl

/-- A primitive scalar layout has nonzero byte size (`== ZERO` is `false`). -/
theorem IsPrimScalarTy.size_beq_zero {ty : Ty} {layouts : LayoutTable}
    (h : IsPrimScalarTy ty) :
    ((translateTy ty layouts).layout.size == Miri.ABI.Size.ZERO) = false :=
  beq_false_of_ne (IsPrimScalarTy.size_ne_zero h)

/-- A primitive scalar layout uses `BackendRepr.Scalar`. -/
theorem IsPrimScalarTy.backendRepr_scalar {ty : Ty} {layouts : LayoutTable}
    (h : IsPrimScalarTy ty) :
    ∃ s, (translateTy ty layouts).layout.backendRepr = .Scalar s := by
  rcases h with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
    (try cases it) <;> (try cases ut) <;> simp [translateTy, hk] <;> exact ⟨_, rfl⟩

private theorem add_size_zero_bytes (x : UInt64) : x + Miri.ABI.Size.ZERO.bytes = x :=
  UInt64.add_zero x

/-- `annealReadImmediateLM2_2` of a field of a memory-backed union (`UnionMemRel`)
reads the field's bytes `[0, w)` (`w` the field's size): when the field is the
one the union holds (`w = k`), it returns the held scalar; when the field is
longer than the initialized prefix (`k < w ≤ S`), the read finds an
uninitialized byte and reports undefined behavior. -/
theorem annealReadImmediate_unionMem
    {m : AnnealStepState} {uTy : Ty} {layouts : LayoutTable} {S : Nat} {f0Ty : Ty}
    {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hnodup : LiveAllocsNodup m.machine)
    (hS : ValidScalarBytes S)
    (hmem : UnionMemRel m.machine uTy layouts S f0Ty sc mp)
    {fty : Ty} (hprim : IsPrimScalarTy fty) {w : Nat} (hw : ValidScalarBytes w)
    (hsz : (translateTy fty layouts).layout.size = translateSizeBytes w) :
    (w = sc.sizeBytes →
      ∃ msc, ScalarRel sc msc ∧
        ImmediateRel f0Ty layouts (.scalar sc) (.scalar (.fromScalarInt msc)) ∧
        annealReadImmediateLM2_2 ⟨.indirect mp, translateTy fty layouts⟩ m =
          .ok ⟨.scalar (.fromScalarInt msc), translateTy fty layouts⟩ m) ∧
    (sc.sizeBytes < w → w ≤ S →
      annealReadImmediateLM2_2 ⟨.indirect mp, translateTy fty layouts⟩ m =
        .error (.undefinedBehavior "read of uninitialized memory field") m) := by
  cases hmem with
  | mk allocId tag baseAddr localAlloc msc hprov _ _ hlive hbase hptr _ hsize hlen _ _ _ _ _
      hk_le hmask hrel _ himm hraw =>
    have hfind := array_find?_of_nodup_fst hnodup hlive
    have hrel_off : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = Miri.ABI.Size.ZERO := by
      have hb : mp.ptr.offset.bytes = baseAddr := by rw [hptr]; rfl
      rw [hb, UInt64.sub_self]; rfl
    have hfields := hprim.fields_primitive (layouts := layouts)
    have hsz0 := hprim.size_beq_zero (layouts := layouts)
    obtain ⟨s_repr, hrepr⟩ := hprim.backendRepr_scalar (layouts := layouts)
    have hS16 : S ≤ 16 := by rcases hS with h | h | h | h | h <;> omega
    have hkv := hrel.validBytes
    have hunfold :
        annealReadImmediateLM2_2 ⟨.indirect mp, translateTy fty layouts⟩ m =
          (match localAlloc.allocation.readScalar annealTargetDataLayout
              (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w)) false with
          | .ok sc => EStateM.Result.ok ⟨.scalar sc, translateTy fty layouts⟩ m
          | .error (.invalidUninitBytes _) =>
              EStateM.Result.error (.undefinedBehavior "read of uninitialized memory field") m
          | .error (.outOfBounds ..) =>
              EStateM.Result.error (.undefinedBehavior "out-of-bounds memory field read") m
          | .error _ => EStateM.Result.error (.unsupported "readScalar failed") m) := by
      unfold annealReadImmediateLM2_2 annealReadIndirectImmediate
      dsimp only
      rw [hprov, hfields, hsz0, hrepr, hsz]
      simp only [Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get,
        bind, EStateM.bind, Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind,
        hrel_off]
      cases localAlloc.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w)) false with
      | ok v => rfl
      | error e => cases e <;> rfl
    refine ⟨fun hwk => ⟨msc, hrel, himm, ?_⟩, fun hlt hwS => ?_⟩
    · subst hwk
      have hinit : localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) =
            .ok (.ok ()) :=
        hmask.init hS hkv hkv hk_le (Nat.le_refl _)
      rw [hunfold, union_readScalar_prefix hrel hlen hsize hS16 hk_le hinit hraw]
    · obtain ⟨bad, hbad⟩ := hmask.uninit hS hkv hw hlt hwS
      rw [hunfold, union_readScalar_uninit hbad]

/-! ## 3. Writing a Scalar Destination -/

/-- `UnionLocalRel` of a local that is not memory-backed is a `LocalRel`. -/
theorem UnionLocalRel.of_immediate
    {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot} {imm : Miri.Interpreter.Immediate AnnealProv}
    {c : Option Miri.Interpreter.LocalLayout}
    (h : UnionLocalRel mach decl layouts slot ⟨.live (.immediate imm), c⟩) :
    LocalRel mach decl layouts slot ⟨.live (.immediate imm), c⟩ := by
  cases h with
  | base _ _ hl => exact hl

/-- The `StateRelLM2_4` counterpart of `write_after_rvalue_simulation_ext`, for
any hooks `H`: once the rvalue of `dst = rv` evaluates to a value related to
`imm`, writing `imm` into the immediate destination `dst` and advancing the
location relates both machines' post-states. -/
theorem write_after_rvalue_simulation_LM2_4
    {PlaceTy : Type}
    (H : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit PlaceTy)
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {tf₀ topFrame₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {val : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    {id0 : Miri.Interpreter.LocalsIdentity}
    {bb : BasicBlockData} {stmt : Statement}
    (hretCont : topFrame₁.returnContinuation = .stop false)
    (hretPlace : ∃ retLay, topFrame₁.returnPlace = .frameLocal 0 0 none retLay topFrame₁.localsIdentity)
    (hcal : s.memory.activeCallee = none)
    (hstack : s.memory.callStack = .nil)
    (hbor : s.memory.borrows = .nil)
    (hprot : s.memory.activeProtectors = .nil)
    (hcaller : s.memory.callerLocals = .nil)
    (hframes : m.stack.frames = #[tf₀])
    (hbody₀ : tf₀.body = translateBody body)
    (hloc₀ : tf₀.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hframe₁ : FrameRelLM2_4 body m.machine s.frame topFrame₁)
    (hdisj : MemoryAllocDisjoint topFrame₁)
    (hdecl : get? body.localDecls dstIdx = some dstDecl)
    (himm_dst : IsImmediateFrameLocal topFrame₁ dstIdx)
    (himmRel : ImmediateRel dstDecl.ty body.layouts val imm)
    (heval_a : evalStmt s stmt body.localDecls body.layouts =
      match get? s.frame.locals dstIdx with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? s.frame.locals dstIdx (.init val) with
        | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub)
    (heval_m : Miri.Interpreter.Step.evalStatement H () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediateLM2_2 imm ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[topFrame₁]⟩ }) :
    StepRelLM2_4 body m
      (evalStmt s stmt body.localDecls body.layouts)
      (Miri.Interpreter.Step.step H () m) ∧
    (Miri.Interpreter.Step.step H () m).1.machine = m.machine ∧
    (∀ j, IsImmediateFrameLocal topFrame₁ j →
      ∀ tf',
        (Miri.Interpreter.Step.step H () m).2 = .ok true →
        (Miri.Interpreter.Step.step H () m).1.stack.frames = #[tf'] →
        IsImmediateFrameLocal tf' j) ∧
    (∀ j, j ≠ dstIdx → ∀ tf',
        (Miri.Interpreter.Step.step H () m).2 = .ok true →
        (Miri.Interpreter.Step.step H () m).1.stack.frames = #[tf'] →
        tf'.locals[j]? = topFrame₁.locals[j]?) := by
  obtain ⟨slot_d, mls_d, hlt_af, hlt_mf, hslot_d, hmls_d, hmls_eq, hloc_d⟩ :=
    hframe₁.lookup_local hdecl
  have hget_d := frame_getLocal_of_getElem? topFrame₁ dstIdx mls_d hmls_d
  have himm_d := himm_dst mls_d hmls_d
  rw [heval_a, hslot_d]
  rcases mls_d with ⟨vd, cd⟩
  cases vd with
  | live op =>
    cases op with
    | indirect mp => exact False.elim (himm_d mp rfl)
    | immediate imm_old =>
      have hloc_base := hloc_d.of_immediate
      obtain ⟨hnot_dead, hval⟩ := hloc_base.immediate_cases
      have hc := hloc_base.cachedLayout_eq
      have hnot_dead' : (match some slot_d with
          | .some .dead => MirStepNode.fail .ub
          | .some _ =>
            match set? s.frame.locals dstIdx (.init val) with
            | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
            | .none => MirStepNode.fail .ub
          | .none => MirStepNode.fail .ub) =
          MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx (.init val)) s.memory) := by
        rcases hval with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;>
          simp [set?_eq_some_set hlt_af]
      rw [hnot_dead']
      let topFrame₂ :=
        { topFrame₁ with
          locals := topFrame₁.locals.set dstIdx
            { topFrame₁.locals[dstIdx]'hlt_mf with value := .live (.immediate imm) } hlt_mf }
      have hm_ok : Miri.Interpreter.Step.evalStatement H () (translateStmt stmt) m =
          ({ m with stack := ⟨#[topFrame₂]⟩ }, .ok ()) := by
        rw [heval_m]
        unfold Miri.Interpreter.runRvalue
        rw [annealWriteImmediateLM2_2_live (topFrame := topFrame₁) rfl hlt_mf hget_d]
      have hloc₁ : topFrame₂.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
        hframe₁.location_eq
      rw [miri_step_at_statement_ok _ hframes hbody₀ hloc₀ hbb hstmt hm_ok rfl hloc₁]
      refine ⟨?_, rfl, ?_, ?_⟩
      · apply StepRelLM2_4.step
        have hloc_new : UnionLocalRel m.machine dstDecl body.layouts (.init val)
            { topFrame₁.locals[dstIdx]'hlt_mf with value := .live (.immediate imm) } := by
          rw [hmls_eq]
          exact .base _ _ (.immediate (.init val) imm cd hc (Or.inr ⟨val, rfl, himmRel⟩))
        have hfr₂ := hframe₁.update_local hdecl (.init val) (.live (.immediate imm)) hloc_new
        obtain ⟨retLay, hretP⟩ := hretPlace
        exact StateRelLM2_4.mk
          { topFrame₂ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
          rfl hretCont ⟨retLay, hretP⟩
          ⟨hfr₂.body_eq, rfl, hfr₂.af_locals_len, hfr₂.mf_locals_size, hfr₂.locals_rel⟩
          hcal hstack hbor hprot hcaller (by
            apply MemoryAllocDisjoint.mono_immediate hdisj
            intro k
            by_cases hk : k = dstIdx
            · subst hk
              right
              exists imm, topFrame₁.locals[k].layout
              dsimp [topFrame₂]
              rw [Array.getElem?_set]
              simp only [↓reduceIte]
            · left
              dsimp [topFrame₂]
              rw [Array.getElem?_set_ne _ (Ne.symm hk)])
      · intro j hj tf' _ htf'
        dsimp only at htf'
        have h_eq : { topFrame₂ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ } =
            tf' := by
          injection htf' with h_arr
          injection h_arr with h_hd _
        subst h_eq
        exact hj.set_immediate hlt_mf imm
      · intro j hj tf' _ htf'
        dsimp only at htf'
        have h_eq : { topFrame₂ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ } =
            tf' := by
          injection htf' with h_arr
          injection h_arr with h_hd _
        subst h_eq
        dsimp [topFrame₂]
        rw [Array.getElem?_set_ne _ (Ne.symm hj)]
  | dead =>
    have hloc_base : LocalRel m.machine dstDecl body.layouts slot_d ⟨.dead, cd⟩ := by
      cases hloc_d with
      | base _ _ hl => exact hl
    cases hloc_base with
    | dead _ _ =>
      have hm_err : Miri.Interpreter.Step.evalStatement H () (translateStmt stmt) m =
          ({ m with stack := ⟨#[topFrame₁]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
        rw [heval_m]
        unfold Miri.Interpreter.runRvalue
        rw [annealWriteImmediateLM2_2_dead (topFrame := topFrame₁) rfl hget_d]
      rw [miri_step_at_statement_error _ hframes hbody₀ hloc₀ hbb hstmt hm_err]
      exact ⟨.ub _ _, rfl, (fun _ _ _ h _ => nomatch h), (fun _ _ _ h _ => nomatch h)⟩

/-! ## 4. Union Field Reads (`union_uninit_bytes_read_ub_simulation`) -/

/-- The operand `copy u.j` (or `move u.j`) reading field `j` of type `fty`. -/
def unionFieldReadOperand (isMove : Bool) (u j : Local) (fty : Ty) : MirAst.Operand :=
  if isMove then .move ⟨u, [.field j fty]⟩ else .copy ⟨u, [.field j fty]⟩

/-- `isUnionLocal` holds for a local declared with a well-typed union type. -/
theorem isUnionLocal_of_wellTyped {body : CapturedMir} {u : Local} {uDecl : LocalDecl}
    {S : Nat} (hdecl : get? body.localDecls u = some uDecl)
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S) :
    isUnionLocal body.localDecls body.layouts u = true := by
  obtain ⟨n, hn, _⟩ := hwt.fields_union
  simp only [isUnionLocal, lookupLocalDeclLayout, hdecl, isUnionLayout, hn]

theorem appendValueList_eq_append : ∀ xs ys : List Value, appendValueList xs ys = xs ++ ys
  | [], _ => rfl
  | x :: xs, ys => congrArg (x :: ·) (appendValueList_eq_append xs ys)

theorem unionSlotFields_eq_list (n f : Nat) (v : Value) :
    unionSlotFields n f v =
      List.replicate f .unit ++ (v :: List.replicate (n - (f + 1)) .unit) := by
  unfold unionSlotFields
  rw [appendValueList_eq_append, replicateValue_eq_replicate, replicateValue_eq_replicate,
    Nat.sub_eq]

theorem unionSlotFields_length {n f : Nat} (hf : f < n) (v : Value) :
    (unionSlotFields n f v).length = n := by
  rw [unionSlotFields_eq_list]
  simp
  omega

theorem unionSlotFields_get_self {n f : Nat} (_hf : f < n) (v : Value) :
    get? (unionSlotFields n f v) f = some v := by
  rw [unionSlotFields_eq_list, get?_eq_getElem?,
    List.getElem?_append_right (by simp)]
  simp

theorem unionSlotFields_get_ne {n f j : Nat} (_hf : f < n) (hj : j < n) (hne : j ≠ f)
    (v : Value) :
    get? (unionSlotFields n f v) j = some .unit := by
  rw [unionSlotFields_eq_list, get?_eq_getElem?]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · rw [List.getElem?_append_left (by simp [hlt]), List.getElem?_replicate]
    simp [hlt]
  · rw [List.getElem?_append_right (by simp; omega)]
    have hk : j - f = (j - (f + 1)) + 1 := by omega
    rw [ List.length_replicate, hk, List.getElem?_cons_succ, List.getElem?_replicate]
    have hlt' : j - (f + 1) < n - (f + 1) := by omega
    simp [hlt']

theorem forceValueListOpt_eq_some : ∀ xs : List Value, forceValueListOpt xs = some xs
  | [] => rfl
  | x :: xs => by
    unfold forceValueListOpt
    rw [forceValueListOpt_eq_some xs]

theorem splitUnionTypedAndOverlay_of_len_eq :
    ∀ {n : Nat} {xs : List Value}, xs.length = n →
      splitUnionTypedAndOverlay n xs = some (xs, none)
  | 0, [], _ => rfl
  | n + 1, x :: xs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    unfold splitUnionTypedAndOverlay
    rw [splitUnionTypedAndOverlay_of_len_eq h]

private theorem unionNonUnitTypedSlotCount_replicate_unit :
    ∀ m k : Nat, unionNonUnitTypedSlotCount m (List.replicate k .unit) = 0
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | m + 1, k + 1 => unionNonUnitTypedSlotCount_replicate_unit m k

private theorem unionNonUnitTypedSlotCount_prefix_scalar (sc : MirAst.ScalarInt) :
    ∀ (f m : Nat) (rest : List Value), f < m →
      unionNonUnitTypedSlotCount m (List.replicate f .unit ++ (.scalar sc :: rest)) =
        1 + unionNonUnitTypedSlotCount (m - (f + 1)) rest
  | 0, m + 1, rest, _ => by
    simp [unionNonUnitTypedSlotCount, Nat.add_comm]
  | f + 1, m + 1, rest, hf => by
    have hf' : f < m := Nat.lt_of_succ_lt_succ hf
    simp only [List.replicate_succ, List.cons_append, unionNonUnitTypedSlotCount,
      Nat.succ_sub_succ_eq_sub]
    exact unionNonUnitTypedSlotCount_prefix_scalar sc f m rest hf'

theorem unionNeedsConsistencyCheck_unionSlotFields_scalar {n f : Nat} (hf : f < n)
    (sc : MirAst.ScalarInt) :
    unionNeedsConsistencyCheck n (unionSlotFields n f (.scalar sc)) = false := by
  unfold unionNeedsConsistencyCheck
  have hlen : length (unionSlotFields n f (.scalar sc)) = n :=
    unionSlotFields_length hf (.scalar sc)
  have hcnt : unionNonUnitTypedSlotCount n (unionSlotFields n f (.scalar sc)) = 1 := by
    rw [unionSlotFields_eq_list, unionNonUnitTypedSlotCount_prefix_scalar sc f n _ hf,
      unionNonUnitTypedSlotCount_replicate_unit]
  rw [hlen, hcnt]
  have hlt_f : Nat.blt n n = false := by
    cases h : Nat.blt n n with
    | false => rfl
    | true => exact absurd (Nat.ble_eq.mp h) (Nat.lt_irrefl n)
  rw [hlt_f]
  rfl

theorem abstractByteEq_refl (b : AbstractByte) : abstractByteEq b b = true := by
  cases b with
  | uninit => rfl
  | init x p =>
    cases p with
    | none => simp [abstractByteEq, abstractByteProvEq]
    | some pt =>
      rcases pt with ⟨a, t⟩
      simp [abstractByteEq, abstractByteProvEq]

theorem abstractByteListEq_refl : ∀ bs : List AbstractByte, abstractByteListEq bs bs = true
  | [] => rfl
  | b :: bs => by
    unfold abstractByteListEq
    simp [abstractByteEq_refl b, abstractByteListEq_refl bs]

theorem takeAbstractBytes_eq_take :
    ∀ (n : Nat) (bs : List AbstractByte), takeAbstractBytes n bs = bs.take n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, b :: bs => congrArg (b :: ·) (takeAbstractBytes_eq_take n bs)

theorem dropAbstractBytes_eq_drop :
    ∀ (n : Nat) (bs : List AbstractByte), dropAbstractBytes n bs = bs.drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: bs => dropAbstractBytes_eq_drop n bs

theorem appendAbstractBytes_eq_append :
    ∀ xs ys : List AbstractByte, appendAbstractBytes xs ys = xs ++ ys
  | [], _ => rfl
  | x :: xs, ys => congrArg (x :: ·) (appendAbstractBytes_eq_append xs ys)

theorem replicateUninitBytes_eq_replicate :
    ∀ n : Nat, replicateUninitBytes n = List.replicate n .uninit
  | 0 => rfl
  | n + 1 => congrArg (.uninit :: ·) (replicateUninitBytes_eq_replicate n)

theorem encodeLittleEndianBytes_length :
    ∀ (x n : Nat) (p : Option (Nat × Nat)), (encodeLittleEndianBytes x n p).length = n
  | _, 0, _ => rfl
  | x, n + 1, p => congrArg (· + 1) (encodeLittleEndianBytes_length (Nat.div x 256) n p)

theorem takeAbstractBytes_encodeLittleEndianBytes :
    ∀ (w k x : Nat) (p : Option (Nat × Nat)), w ≤ k →
      takeAbstractBytes w (encodeLittleEndianBytes x k p) = encodeLittleEndianBytes x w p
  | 0, _, _, _, _ => rfl
  | _ + 1, 0, _, _, h => absurd h (by omega)
  | w + 1, k + 1, x, p, h =>
    congrArg (.init (UInt8.ofNat x) p :: ·)
      (takeAbstractBytes_encodeLittleEndianBytes w k (Nat.div x 256) p (Nat.le_of_succ_le_succ h))

theorem decodeLittleEndianBytes_encodeLittleEndianBytes_none :
    ∀ (w x : Nat),
      decodeLittleEndianBytes (encodeLittleEndianBytes x w none) =
        some (x % scalarModulus w, none)
  | 0, x => by
    rw [scalarModulus_eq_two_pow]
    exact congrArg (fun v => some (v, none)) (Nat.mod_one x).symm
  | w + 1, x => by
    unfold encodeLittleEndianBytes decodeLittleEndianBytes
    change (match decodeLittleEndianBytes (encodeLittleEndianBytes (x / 256) w none) with
      | some (highBits, restProv) =>
        some ((UInt8.ofNat x).toBitVec.toNat + 256 * highBits, mergeByteProvenance none restProv)
      | none => none) = _
    rw [decodeLittleEndianBytes_encodeLittleEndianBytes_none w (x / 256)]
    dsimp only [mergeByteProvenance]
    simp only [scalarModulus_eq_two_pow]
    have hu8 : (UInt8.ofNat x).toBitVec.toNat = x % 256 := by simp [UInt8.ofNat]
    rw [hu8]
    congr 1; congr 1
    let M := 2 ^ (8 * w)
    have hpow : 2 ^ (8 * (w + 1)) = 256 * M := by
      dsimp only [M]
      rw [show 8 * (w + 1) = 8 + 8 * w by omega, Nat.pow_add]
    rw [hpow]
    have hM : 0 < M := Nat.two_pow_pos _
    have hb : x % 256 < 256 := Nat.mod_lt x (by decide)
    have hr : (x / 256) % M < M := Nat.mod_lt _ hM
    have hlt : x % 256 + 256 * ((x / 256) % M) < 256 * M := by
      have := Nat.mul_le_mul_left 256 (Nat.succ_le_of_lt hr)
      omega
    have hx : x = (x % 256 + 256 * ((x / 256) % M)) + ((x / 256) / M) * (256 * M) := by
      have h1 := (Nat.mod_add_div x 256).symm
      have h2 := (Nat.mod_add_div (x / 256) M).symm
      rw [h2, Nat.left_distrib, ← Nat.add_assoc] at h1
      have hmul : 256 * (M * ((x / 256) / M)) = ((x / 256) / M) * (256 * M) := by
        rw [Nat.mul_comm _ (256 * M), Nat.mul_assoc]
      rwa [hmul] at h1
    conv => rhs; rw [hx]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

theorem decodeLittleEndianBytes_append_uninit :
    ∀ (xs ys : List AbstractByte), decodeLittleEndianBytes (xs ++ .uninit :: ys) = none
  | [], _ => rfl
  | .uninit :: _, _ => rfl
  | .init b p :: rest, ys => by
    simp [decodeLittleEndianBytes, decodeLittleEndianBytes_append_uninit rest ys]

theorem abstractBytesHaveProv_encodeLittleEndian_none :
    ∀ (x n : Nat), abstractBytesHaveProv (encodeLittleEndianBytes x n none) = false
  | _, 0 => rfl
  | x, n + 1 => abstractBytesHaveProv_encodeLittleEndian_none (Nat.div x 256) n

theorem resolveTyWithLocalDecls_kind_eq (localDecls : List LocalDecl) (layouts : LayoutTable)
    (ty : Ty) : (resolveTyWithLocalDecls localDecls layouts ty).kind = ty.kind := by
  unfold resolveTyWithLocalDecls
  cases isUnresolvedLayoutIdx layouts ty.layoutIdx
  · rfl
  · cases findDeclOrContainerElemTyWithKind? localDecls layouts ty.kind
    · cases Nat.beq ty.layoutIdx 0 <;> cases localDecls <;>
        (try cases isPrimitiveScalarKind ty.kind) <;> rfl
    · rfl

theorem resolveTyWithLocalDecls_of_union {localDecls : List LocalDecl} {layouts : LayoutTable}
    {uTy : Ty} {S : Nat} (hwt : WellTypedUnionTy layouts uTy S) :
    resolveTyWithLocalDecls localDecls layouts uTy = uTy := by
  obtain ⟨_, _, tl, _, _, hpos, _, hlookup, _, _, _, _, _, _, _, _⟩ := hwt.adt_spec
  have h0 : Nat.beq uTy.layoutIdx 0 = false := by
    cases h : Nat.beq uTy.layoutIdx 0 with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true h ▸ hpos) (Nat.lt_irrefl 0)
  unfold resolveTyWithLocalDecls isUnresolvedLayoutIdx
  simp [h0, hlookup]

theorem placeTouchesUnion_union_field {body : CapturedMir} {u : Local} {uDecl : LocalDecl}
    {S : Nat} (hdecl_u : get? body.localDecls u = some uDecl)
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S) (j : Nat) (fty : Ty) :
    placeTouchesUnion body.localDecls body.layouts ⟨u, [.field j fty]⟩ = true := by
  obtain ⟨defPath, args, tl, n, hk, _, _, hlookup, hfu, _, _, _, _, _, _, _⟩ := hwt.adt_spec
  have hdecls_ne : ∃ d0 ds, body.localDecls = d0 :: ds := by
    cases h : body.localDecls with
    | nil => rw [h] at hdecl_u; cases hdecl_u
    | cons d0 ds => exact ⟨d0, ds, rfl⟩
  obtain ⟨d0, ds, hd⟩ := hdecls_ne
  have hr := resolveTyWithLocalDecls_of_union (localDecls := body.localDecls) hwt
  unfold placeTouchesUnion
  rw [hd]; dsimp only
  rw [← hd, hdecl_u]; dsimp only
  unfold tyProjTouchesUnion
  dsimp only
  rw [hr]
  unfold Trusted.Rustc.V2026_06_01.MirSemantics.isUnionLayout
  rw [hk, hlookup]
  cases tl
  dsimp only at hfu ⊢
  subst hfu
  cases he : body.layouts.entries with
  | nil => simp [LayoutTable.lookup, he, get?] at hlookup
  | cons _ _ => rfl

theorem tyProjTouchesUnion_subslice_nil (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy : Ty) (fromIdx toIdx : Nat) (fromEnd : Bool) :
    tyProjTouchesUnion localDecls layouts baseTy [.subslice fromIdx toIdx fromEnd] = false := rfl

theorem placeTouchesUnion_subslice_single (localDecls : List LocalDecl) (layouts : LayoutTable)
    (loc : Local) (fromIdx toIdx : Nat) (fromEnd : Bool) :
    placeTouchesUnion localDecls layouts ⟨loc, [.subslice fromIdx toIdx fromEnd]⟩ = false := by
  unfold placeTouchesUnion
  cases localDecls with
  | nil => rfl
  | cons d ds =>
    cases layouts.entries with
    | nil => rfl
    | cons e es =>
      cases get? (d :: ds) loc <;> rfl

theorem placeTouchesUnion_subslice_constIndex (localDecls : List LocalDecl) (layouts : LayoutTable)
    (loc : Local) (fromIdx toIdx off minLen : Nat) (fromEnd ciFromEnd : Bool) :
    placeTouchesUnion localDecls layouts
      ⟨loc, [.subslice fromIdx toIdx fromEnd, .constantIndex off minLen ciFromEnd]⟩ = false := by
  have hty : ∀ baseTy,
      tyProjTouchesUnion localDecls layouts baseTy
        [.subslice fromIdx toIdx fromEnd, .constantIndex off minLen ciFromEnd] = false := by
    intro baseTy
    show tyProjTouchesUnion localDecls layouts baseTy
      [.constantIndex off minLen ciFromEnd] = false
    unfold tyProjTouchesUnion
    dsimp only
    cases elemTyOf (resolveTyWithLocalDecls localDecls layouts baseTy) with
    | none => rfl
    | some et => cases et; rfl
  unfold placeTouchesUnion
  cases localDecls with
  | nil => rfl
  | cons d ds =>
    cases layouts.entries with
    | nil => rfl
    | cons e es =>
      cases get? (d :: ds) loc with
      | none => rfl
      | some decl => exact hty decl.ty

private theorem primScalar_width_eq {layouts : LayoutTable} {fty : Ty} {w : Nat}
    (_hprim : IsPrimScalarTy fty) (hw : ValidScalarBytes w)
    (hsz : (translateTy fty layouts).layout.size = translateSizeBytes w) :
    (fty.kind = .bool → w = 1) ∧
    (fty.kind = .char → w = 4) ∧
    (∀ it, fty.kind = .int it → intCastTargetBytes (.int it) = some w) ∧
    (∀ ut, fty.kind = .uint ut → intCastTargetBytes (.uint ut) = some w) := by
  have hinj : ∀ k : Nat, ValidScalarBytes k →
      (translateTy fty layouts).layout.size = translateSizeBytes k → w = k :=
    fun k hk h => translateSizeBytes_inj hw hk (hsz.symm.trans h)
  refine ⟨fun hk => ?_, fun hk => ?_, fun it hk => ?_, fun ut hk => ?_⟩
  · exact hinj 1 (Or.inl rfl) (by simp [translateTy, hk]; rfl)
  · exact hinj 4 (Or.inr (Or.inr (Or.inl rfl))) (by simp [translateTy, hk]; rfl)
  · cases it
    · rw [hinj 1 (Or.inl rfl) (by simp [translateTy, hk]; rfl)]; rfl
    · rw [hinj 2 (Or.inr (Or.inl rfl)) (by simp [translateTy, hk]; rfl)]; rfl
    · rw [hinj 4 (Or.inr (Or.inr (Or.inl rfl))) (by simp [translateTy, hk]; rfl)]; rfl
    · rw [hinj 8 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by simp [translateTy, hk]; rfl)]; rfl
    · rw [hinj 16 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by simp [translateTy, hk]; rfl)]; rfl
    · rw [hinj 8 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by simp [translateTy, hk]; rfl)]; rfl
  · cases ut
    · rw [hinj 1 (Or.inl rfl) (by simp [translateTy, hk]; rfl)]; rfl
    · rw [hinj 2 (Or.inr (Or.inl rfl)) (by simp [translateTy, hk]; rfl)]; rfl
    · rw [hinj 4 (Or.inr (Or.inr (Or.inl rfl))) (by simp [translateTy, hk]; rfl)]; rfl
    · rw [hinj 8 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by simp [translateTy, hk]; rfl)]; rfl
    · rw [hinj 16 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by simp [translateTy, hk]; rfl)]; rfl
    · rw [hinj 8 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by simp [translateTy, hk]; rfl)]; rfl

theorem tyByteSize_primScalar {localDecls : List LocalDecl} {layouts : LayoutTable}
    {fty rTy : Ty} {w : Nat} (hprim : IsPrimScalarTy fty) (hw : ValidScalarBytes w)
    (hsz : (translateTy fty layouts).layout.size = translateSizeBytes w)
    (hrk : rTy.kind = fty.kind) :
    tyByteSize localDecls layouts rTy = some w := by
  obtain ⟨hbool_w, hchar_w, hint_w, huint_w⟩ := primScalar_width_eq hprim hw hsz
  have hrk' : (resolveTyWithLocalDecls localDecls layouts rTy).kind = fty.kind := by
    rw [resolveTyWithLocalDecls_kind_eq, hrk]
  have hkind_sz : rigidTyKindByteSize fty.kind = some w := by
    rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · rw [hk, hbool_w hk]
    · rw [hk, hchar_w hk]
    · rw [hk]; unfold rigidTyKindByteSize; exact hint_w it hk
    · rw [hk]; unfold rigidTyKindByteSize; exact huint_w ut hk
  unfold tyByteSize tyByteSizeAndAlignAux
  generalize resolveTyWithLocalDecls localDecls layouts rTy = rResolved at hrk' ⊢
  rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
    rw [hk] at hrk' hkind_sz <;>
    simp [hrk', rigidTyByteSize, hkind_sz]

theorem encodeTypedValueToBytes_primScalar {layouts : LayoutTable} {fty rTy : Ty}
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hprim : IsPrimScalarTy fty)
    (himm : ImmediateRel fty layouts (.scalar sc) (.scalar (.fromScalarInt msc)))
    (hrk : rTy.kind = fty.kind) :
    encodeTypedValueToBytes layouts rTy (.scalar sc) =
      some (encodeLittleEndianBytes sc.bits sc.sizeBytes none) := by
  cases himm with
  | scalar _ _ hrel hsz_ty hbool hchar =>
  have hvb := hrel.validBytes
  obtain ⟨_, _, hint_w, huint_w⟩ := primScalar_width_eq hprim hvb hsz_ty
  have h0 : Nat.beq sc.sizeBytes 0 = false := by
    rcases hvb with h | h | h | h | h <;> (rw [h]; rfl)
  unfold encodeTypedValueToBytes
  dsimp only
  rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
  · have hrk' : rTy.kind = .bool := hrk.trans hk
    obtain ⟨h1, hb⟩ := hbool hk
    have hnr : normalizeCodecTy rTy = rTy := by unfold normalizeCodecTy; rw [hrk']
    have hu : Trusted.Rustc.V2026_06_01.MirSemantics.isUnionLayout layouts rTy = false := by
      unfold Trusted.Rustc.V2026_06_01.MirSemantics.isUnionLayout; rw [hrk']
    rw [hnr, hu]
    rcases hb with hb0 | hb1
    · simp [encodeValueToBytes, hrk', h1, hb0, encodeLittleEndianBytes]
    · simp [encodeValueToBytes, hrk', h1, hb1, encodeLittleEndianBytes]
  · have hrk' : rTy.kind = .char := hrk.trans hk
    obtain ⟨h4, hc⟩ := hchar hk
    have hnr : normalizeCodecTy rTy = rTy := by unfold normalizeCodecTy; rw [hrk']
    have hu : Trusted.Rustc.V2026_06_01.MirSemantics.isUnionLayout layouts rTy = false := by
      unfold Trusted.Rustc.V2026_06_01.MirSemantics.isUnionLayout; rw [hrk']
    rw [hnr, hu]
    simp [encodeValueToBytes, hrk', h4, hc, encodeScalarBytes]
  · have hrk' : rTy.kind = .int it := hrk.trans hk
    have hnr : normalizeCodecTy rTy = rTy := by unfold normalizeCodecTy; rw [hrk']
    have hu : Trusted.Rustc.V2026_06_01.MirSemantics.isUnionLayout layouts rTy = false := by
      unfold Trusted.Rustc.V2026_06_01.MirSemantics.isUnionLayout; rw [hrk']
    rw [hnr, hu]
    simp [encodeValueToBytes, hrk', hint_w it hk, encodeScalarBytes, h0]
  · have hrk' : rTy.kind = .uint ut := hrk.trans hk
    have hnr : normalizeCodecTy rTy = rTy := by unfold normalizeCodecTy; rw [hrk']
    have hu : Trusted.Rustc.V2026_06_01.MirSemantics.isUnionLayout layouts rTy = false := by
      unfold Trusted.Rustc.V2026_06_01.MirSemantics.isUnionLayout; rw [hrk']
    rw [hnr, hu]
    simp [encodeValueToBytes, hrk', huint_w ut hk, encodeScalarBytes, h0]

theorem decodeTypedValueFromBytes_primScalar {layouts : LayoutTable} {fty rTy : Ty}
    {x w : Nat} (hprim : IsPrimScalarTy fty) (hw : ValidScalarBytes w)
    (hsz : (translateTy fty layouts).layout.size = translateSizeBytes w)
    (hrk : rTy.kind = fty.kind)
    (hbool : fty.kind = .bool → x % scalarModulus w = 0 ∨ x % scalarModulus w = 1)
    (hchar : fty.kind = .char → isValidCharCode (x % scalarModulus w) = true) :
    decodeTypedValueFromBytes defaultCodecFuel layouts rTy
        (encodeLittleEndianBytes x w none) =
      some (.scalar ⟨x % scalarModulus w, w⟩) := by
  obtain ⟨hbool_w, hchar_w, hint_w, huint_w⟩ := primScalar_width_eq hprim hw hsz
  have hlen_list := encodeLittleEndianBytes_length x w none
  have hlen : length (encodeLittleEndianBytes x w none) = w := hlen_list
  have hw0 : Nat.beq w 0 = false := by rcases hw with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hprov := abstractBytesHaveProv_encodeLittleEndian_none x w
  have hdec := decodeLittleEndianBytes_encodeLittleEndianBytes_none w x
  have hdec_sc : ∀ s, decodeScalarBytes (encodeLittleEndianBytes x w none) s =
      some (⟨x % scalarModulus w, w⟩, none) := by
    intro s; unfold decodeScalarBytes; dsimp only
    rw [hlen, hw0, hdec]
  cases rTy with | mk rk rl =>
  dsimp only at hrk
  show decodeTypedValueFromBytes (15 + 1) layouts ⟨rk, rl⟩ (encodeLittleEndianBytes x w none) =
    some (.scalar ⟨x % scalarModulus w, w⟩)
  unfold decodeTypedValueFromBytes
  rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
  · have hw1 := hbool_w hk; subst hw1
    have hrk' : rk = .bool := hrk.trans hk; subst hrk'
    dsimp only [normalizeCodecTy]
    unfold decodeValueFromBytes
    dsimp only [encodeLittleEndianBytes]
    have hu8 : (UInt8.ofNat x).toBitVec.toNat = x % scalarModulus 1 := by
      rw [scalarModulus_eq_two_pow]; simp [UInt8.ofNat]
    rw [hu8]
    rcases hbool hk with hb0 | hb1
    · rw [hb0]
    · rw [hb1]
  · have hw4 := hchar_w hk; subst hw4
    have hrk' : rk = .char := hrk.trans hk; subst hrk'
    dsimp only [normalizeCodecTy]
    unfold decodeValueFromBytes
    dsimp only
    rw [hlen, Nat.beq_refl]; dsimp only
    rw [hdec_sc]; dsimp only
    rw [hchar hk]
  · have hrk' : rk = .int it := hrk.trans hk; subst hrk'
    dsimp only [normalizeCodecTy]
    rw [hprov]; dsimp only
    unfold decodeValueFromBytes
    dsimp only
    rw [hint_w it hk]; dsimp only
    rw [hlen, Nat.beq_refl]; dsimp only
    rw [hdec_sc]
  · have hrk' : rk = .uint ut := hrk.trans hk; subst hrk'
    dsimp only [normalizeCodecTy]
    rw [hprov]; dsimp only
    unfold decodeValueFromBytes
    dsimp only
    rw [huint_w ut hk]; dsimp only
    rw [hlen, Nat.beq_refl]; dsimp only
    rw [hdec_sc]

theorem decodeTypedValueFromBytes_primScalar_uninit {layouts : LayoutTable} {fty rTy : Ty}
    (hprim : IsPrimScalarTy fty) (hrk : rTy.kind = fty.kind)
    (xs ys : List AbstractByte) (hnot_bool : fty.kind ≠ .bool) :
    decodeTypedValueFromBytes defaultCodecFuel layouts rTy (xs ++ .uninit :: ys) = none := by
  have hdec := decodeLittleEndianBytes_append_uninit xs ys
  have hdec_sc : ∀ s, decodeScalarBytes (xs ++ .uninit :: ys) s = none := by
    intro s; unfold decodeScalarBytes; dsimp only
    cases Nat.beq (length (xs ++ .uninit :: ys)) 0 <;> simp [hdec]
  cases rTy with | mk rk rl =>
  dsimp only at hrk
  show decodeTypedValueFromBytes (15 + 1) layouts ⟨rk, rl⟩ (xs ++ .uninit :: ys) = none
  unfold decodeTypedValueFromBytes
  rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
  · exact absurd hk hnot_bool
  · have hrk' : rk = .char := hrk.trans hk; subst hrk'
    dsimp only [normalizeCodecTy]
    cases hp : abstractBytesHaveProv (xs ++ .uninit :: ys)
    · dsimp only; unfold decodeValueFromBytes; dsimp only
      cases h4 : Nat.beq (length (xs ++ .uninit :: ys)) 4
      · rfl
      · dsimp only; rw [hdec_sc]
    · rfl
  · have hrk' : rk = .int it := hrk.trans hk; subst hrk'
    dsimp only [normalizeCodecTy]
    cases hp : abstractBytesHaveProv (xs ++ .uninit :: ys)
    · dsimp only; unfold decodeValueFromBytes; dsimp only
      cases intCastTargetBytes (.int it) with
      | none => rfl
      | some eb =>
        dsimp only
        cases Nat.beq (length (xs ++ .uninit :: ys)) eb
        · rfl
        · dsimp only; rw [hdec_sc]
    · rfl
  · have hrk' : rk = .uint ut := hrk.trans hk; subst hrk'
    dsimp only [normalizeCodecTy]
    cases hp : abstractBytesHaveProv (xs ++ .uninit :: ys)
    · dsimp only; unfold decodeValueFromBytes; dsimp only
      cases intCastTargetBytes (.uint ut) with
      | none => rfl
      | some eb =>
        dsimp only
        cases Nat.beq (length (xs ++ .uninit :: ys)) eb
        · rfl
        · dsimp only; rw [hdec_sc]
    · rfl

private theorem mergeMaskedAbstractBytes_fresh :
    ∀ (bs : List AbstractByte) (S : Nat) (bmList : List Bool),
      (∀ b ∈ bs, ∃ x p, b = .init x p) →
      bs.length ≤ S →
      mergeMaskedAbstractBytes (replicateUninitBytes S) (replicateBool S false) bs bmList =
        some (bs ++ replicateUninitBytes (S - bs.length),
          List.replicate bs.length true ++ replicateBool (S - bs.length) false)
  | [], S, _, _, _ => by simp [mergeMaskedAbstractBytes]
  | _ :: _, 0, _, _, hle => absurd hle (by simp)
  | b :: bs, S + 1, bmList, hinit, hle => by
    obtain ⟨x, p, rfl⟩ := hinit b List.mem_cons_self
    have hle' : bs.length ≤ S := Nat.le_of_succ_le_succ hle
    have hih := mergeMaskedAbstractBytes_fresh bs S
      (match bmList with | _ :: r => r | [] => [])
      (fun b' hb' => hinit b' (List.mem_cons_of_mem _ hb')) hle'
    simp only [List.length_cons, Nat.succ_sub_succ_eq_sub, List.replicate_succ, List.cons_append]
    cases bmList <;>
      (dsimp only [replicateUninitBytes, replicateBool, mergeMaskedAbstractBytes] at hih ⊢;
       rw [hih])

private theorem encodeLittleEndianBytes_all_init :
    ∀ (x n : Nat) (p : Option (Nat × Nat)) (b : AbstractByte),
      b ∈ encodeLittleEndianBytes x n p → ∃ y q, b = .init y q
  | _, 0, _, _, h => nomatch h
  | x, n + 1, p, b, h => by
    rcases List.mem_cons.mp h with rfl | hrest
    · exact ⟨_, _, rfl⟩
    · exact encodeLittleEndianBytes_all_init (Nat.div x 256) n p b hrest

private theorem mergeUnionTypedSlotsAux_units (layouts : LayoutTable)
    (enc : Nat → Value → Option (List AbstractByte)) (fb : Nat) (ov : Bool) (S : Nat) :
    ∀ (k : Nat) (flIdxs : List Nat) (rest : List Value) (buf : List AbstractByte)
      (bufMask : List Bool),
      mergeUnionTypedSlotsAux layouts enc fb ov S flIdxs (List.replicate k .unit ++ rest) buf
          bufMask =
        mergeUnionTypedSlotsAux layouts enc fb ov S (flIdxs.drop k) rest buf bufMask
  | 0, _, _, _, _ => rfl
  | k + 1, [], rest, buf, bufMask => by
    simp only [List.replicate_succ, List.cons_append, mergeUnionTypedSlotsAux, List.drop_nil]
    have h := mergeUnionTypedSlotsAux_units layouts enc fb ov S k [] rest buf bufMask
    simpa only [List.drop_nil] using h
  | k + 1, _ :: flRest, rest, buf, bufMask =>
    mergeUnionTypedSlotsAux_units layouts enc fb ov S k flRest rest buf bufMask

theorem unionFieldLayoutOf_lookup_eq {layouts : LayoutTable} {uTy : Ty} {S f : Nat}
    {fl : Miri.Interpreter.LocalLayout}
    (hwt : WellTypedUnionTy layouts uTy S)
    (hfl : unionFieldLayoutOf layouts (translateTy uTy layouts) f = some fl) :
    ∃ tl flIdx fTl,
      layouts.lookup uTy.layoutIdx = some tl ∧
      get? tl.fieldLayouts f = some flIdx ∧
      layouts.lookup flIdx = some fTl ∧
      fl = { ty := 100 + flIdx, layout := translateTypeLayout fTl } := by
  obtain ⟨defPath, args, tl, n, hk, hpos, hlt900, hlookup, _, _, _, _, _, _, _, _⟩ := hwt.adt_spec
  have hty_id : (translateTy uTy layouts).ty = 100 + uTy.layoutIdx := by
    unfold translateTy encodeTyId
    rw [hk, hlookup]
  unfold unionFieldLayoutOf at hfl
  rw [hty_id] at hfl
  have hcond : 100 ≤ 100 + uTy.layoutIdx ∧ 100 + uTy.layoutIdx < 1000 :=
    ⟨Nat.le_add_right 100 uTy.layoutIdx, Nat.add_lt_add_left hlt900 100⟩
  simp only [hcond, and_self, ↓reduceIte, Nat.add_sub_cancel_left, hlookup] at hfl
  cases hgf : get? tl.fieldLayouts f with
  | none => rw [hgf] at hfl; cases hfl
  | some flIdx =>
    rw [hgf] at hfl
    dsimp only at hfl
    cases hlf : layouts.lookup flIdx with
    | none => rw [hlf] at hfl; cases hfl
    | some fTl =>
      rw [hlf] at hfl
      simp only [Option.map, Option.some.injEq] at hfl
      exact ⟨tl, flIdx, fTl, hlookup, hgf, hlf, hfl.symm⟩

private theorem list_drop_of_get? {α : Type} {x : α} :
    ∀ (xs : List α) (f : Nat), get? xs f = some x → xs.drop f = x :: xs.drop (f + 1)
  | [], _, h => nomatch h
  | _ :: _, 0, h => by injection h with h; subst h; rfl
  | _ :: xs, f + 1, h => list_drop_of_get? xs f h

private theorem mergeUnionTypedSlotsAux_units_nil (layouts : LayoutTable)
    (enc : Nat → Value → Option (List AbstractByte)) (fb : Nat) (ov : Bool) (S : Nat)
    (k : Nat) (flIdxs : List Nat) (buf : List AbstractByte) (bufMask : List Bool) :
    mergeUnionTypedSlotsAux layouts enc fb ov S flIdxs (List.replicate k .unit) buf bufMask =
      some buf := by
  have h := mergeUnionTypedSlotsAux_units layouts enc fb ov S k flIdxs [] buf bufMask
  simpa [mergeUnionTypedSlotsAux] using h

theorem encodeByLayoutIdxAux_union_nil {layouts : LayoutTable} {uTy : Ty} {S : Nat}
    (hwt : WellTypedUnionTy layouts uTy S) :
    encodeByLayoutIdxAux 8 layouts uTy.layoutIdx (.aggregate 0 []) =
      some (replicateUninitBytes S) := by
  obtain ⟨_, _, tl, n, hk, _, _, hlookup, hfu, _, huninh, htl_sz, hfl_len, _, _, _⟩ :=
    hwt.adt_spec
  obtain ⟨n2, hfields2, hn2⟩ := hwt.fields_union
  have hn_eq : n2 = n := by
    unfold translateTy at hfields2
    dsimp only at hfields2
    rw [hk, hlookup] at hfields2
    dsimp only [translateTypeLayout, translateFieldsShape] at hfields2
    rw [hfu] at hfields2
    cases hfields2
    rfl
  simp only [hn_eq] at *
  have hfls_ne : ∃ a as, tl.fieldLayouts = a :: as := by
    cases h : tl.fieldLayouts with
    | nil =>
      have h0 : 0 = n := by rw [← hfl_len, h]; rfl
      rw [← h0] at hn2; cases hn2
    | cons a as => exact ⟨a, as, rfl⟩
  obtain ⟨a, as, hfls_eq⟩ := hfls_ne
  have hsplit : splitUnionTypedAndOverlay n [] = some ([], none) := by cases n <;> rfl
  unfold encodeByLayoutIdxAux encodeUnionSlotsIntoBufAux
  dsimp only
  rw [hlookup]
  dsimp only
  rw [huninh, hfu]
  dsimp only
  rw [hsplit]
  dsimp only
  rw [hfls_eq]
  dsimp only
  rw [← hfls_eq, htl_sz]
  rfl

theorem encodeByLayoutIdxAux_unionSlotFields {layouts : LayoutTable} {uTy fTy : Ty}
    {S n f : Nat} {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hwt : WellTypedUnionTy layouts uTy S)
    (hfields : (translateTy uTy layouts).layout.fields = .Union n)
    (hf : f < n)
    (hprim : IsPrimScalarTy fTy)
    (himm : ImmediateRel fTy layouts (.scalar sc) (.scalar (.fromScalarInt msc)))
    (hfl : ∃ fl, unionFieldLayoutOf layouts (translateTy uTy layouts) f = some fl ∧
      fl.layout.size = (translateTy fTy layouts).layout.size) :
    encodeByLayoutIdxAux 8 layouts uTy.layoutIdx
        (.aggregate 0 (unionSlotFields n f (.scalar sc))) =
      some (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
        replicateUninitBytes (S - sc.sizeBytes)) := by
  obtain ⟨fl, hfl_eq, hfl_sz⟩ := hfl
  obtain ⟨tl', flIdx, fTl, hlookup', hgf, hlf, rfl⟩ := unionFieldLayoutOf_lookup_eq hwt hfl_eq
  obtain ⟨defPath, args, tl, n', hk, _, _, hlookup, hfu, _, huninh, htl_sz, hfl_len, _, _,
    hadt_fields⟩ := hwt.adt_spec
  rw [hlookup] at hlookup'; injection hlookup' with htl_eq; subst htl_eq
  have hn_eq : n' = n := by
    unfold translateTy at hfields
    dsimp only at hfields
    rw [hk, hlookup] at hfields
    dsimp only [translateTypeLayout, translateFieldsShape] at hfields
    rw [hfu] at hfields
    cases hfields
    rfl
  simp only [hn_eq] at *
  obtain ⟨fTl', hlf', _, hvb_f, hfTl_le, henc_slot⟩ := hadt_fields f flIdx hgf
  rw [hlf] at hlf'; injection hlf' with hfTl_eq; subst hfTl_eq
  cases himm with
  | scalar _ _ hrel_sc hsz_fTy hbool_sc hchar_sc =>
  have himm : ImmediateRel fTy layouts (.scalar sc) (.scalar (.fromScalarInt msc)) :=
    .scalar sc msc hrel_sc hsz_fTy hbool_sc hchar_sc
  have hvb_sc : ValidScalarBytes sc.sizeBytes := hrel_sc.validBytes
  have hsc_sz : sc.sizeBytes = fTl.size.bytes :=
    translateSizeBytes_inj hvb_sc hvb_f (hsz_fTy.symm.trans hfl_sz.symm)
  have henc7 := henc_slot fTy sc msc hprim himm hsc_sz 6
  have h0 : Nat.beq sc.sizeBytes 0 = false := by
    rcases hvb_sc with h | h | h | h | h <;> (rw [h]; rfl)
  have henc_sc : encodeScalarBytes sc none =
      some (encodeLittleEndianBytes sc.bits sc.sizeBytes none) := by
    simp [encodeScalarBytes, h0]
  have hfls_ne : ∃ a as, tl.fieldLayouts = a :: as := by
    cases h : tl.fieldLayouts with
    | nil =>
      have h0' : 0 = n := by rw [← hfl_len, h]; rfl
      rw [← h0'] at hf; cases hf
    | cons a as => exact ⟨a, as, rfl⟩
  obtain ⟨a, as, hfls_eq⟩ := hfls_ne
  have hsplit := splitUnionTypedAndOverlay_of_len_eq (unionSlotFields_length hf (.scalar sc))
  have hdrop := list_drop_of_get? tl.fieldLayouts f hgf
  have hle_S : (encodeLittleEndianBytes sc.bits sc.sizeBytes none).length ≤ S := by
    rw [encodeLittleEndianBytes_length, hsc_sz]; exact hfTl_le
  have hmerge := mergeMaskedAbstractBytes_fresh
    (encodeLittleEndianBytes sc.bits sc.sizeBytes none) S
    (layoutValueMaskAux 8 layouts flIdx)
    (encodeLittleEndianBytes_all_init sc.bits sc.sizeBytes none) hle_S
  unfold encodeByLayoutIdxAux encodeUnionSlotsIntoBufAux
  dsimp only
  rw [hlookup]
  dsimp only
  rw [huninh, hfu]
  dsimp only
  rw [hsplit]
  dsimp only
  rw [hfls_eq]
  dsimp only
  rw [← hfls_eq, htl_sz, unionSlotFields_eq_list, mergeUnionTypedSlotsAux_units, hdrop]
  dsimp only [mergeUnionTypedSlotsAux]
  rw [henc7, henc_sc]; dsimp only
  rw [hmerge]; dsimp only
  rw [encodeLittleEndianBytes_length, mergeUnionTypedSlotsAux_units_nil]

theorem placeTyResolved_field_kind {localDecls : List LocalDecl} {layouts : LayoutTable}
    {u : Local} {uDecl : LocalDecl} (hdecl_u : get? localDecls u = some uDecl)
    (j : Nat) (fty : Ty) :
    ∃ rTy, placeTyResolved localDecls layouts ⟨u, [.field j fty]⟩ = some rTy ∧
      rTy.kind = fty.kind := by
  unfold placeTyResolved
  rw [hdecl_u]
  dsimp only
  unfold resolveProjectedTyResolved
  cases h : isUnresolvedLayoutIdx layouts fty.layoutIdx
  · dsimp only
    exact ⟨fty, rfl, rfl⟩
  · dsimp only
    cases hl : layouts.lookup uDecl.ty.layoutIdx with
    | none =>
      dsimp only
      exact ⟨_, rfl, resolveTyWithLocalDecls_kind_eq localDecls layouts fty⟩
    | some l =>
      dsimp only
      cases hv : l.variants with
      | single _ =>
        dsimp only
        cases hg : get? l.fieldLayouts j with
        | none =>
          dsimp only
          exact ⟨_, rfl, resolveTyWithLocalDecls_kind_eq localDecls layouts fty⟩
        | some flIdx =>
          dsimp only
          exact ⟨{ fty with layoutIdx := flIdx }, rfl, rfl⟩
      | _ =>
        dsimp only
        exact ⟨_, rfl, resolveTyWithLocalDecls_kind_eq localDecls layouts fty⟩

theorem validateValueForTy?_primScalar (layouts : LayoutTable) {fty : Ty} {tyOpt : Option Ty}
    {bits w : Nat} (hprim : IsPrimScalarTy fty) (hw : ValidScalarBytes w)
    (hsz : (translateTy fty layouts).layout.size = translateSizeBytes w)
    (hk_opt : ∀ rTy, tyOpt = some rTy → rTy.kind = fty.kind)
    (hbool : fty.kind = .bool → bits = 0 ∨ bits = 1)
    (hchar : fty.kind = .char → isValidCharCode bits = true) :
    validateValueForTy? layouts tyOpt (.scalar ⟨bits, w⟩) = true := by
  cases tyOpt with
  | none => rfl
  | some rTy =>
    have hrk := hk_opt rTy rfl
    cases rTy with | mk rk rl =>
    dsimp only at hrk
    unfold validateValueForTy?
    rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · have hw1 : w = 1 := translateSizeBytes_inj hw (Or.inl rfl)
        (by rw [← hsz]; simp [translateTy, hk]; rfl)
      subst hw1
      have hrk' : rk = .bool := hrk.trans hk
      subst hrk'
      rcases hbool hk with rfl | rfl <;> rfl
    · have hw4 : w = 4 := translateSizeBytes_inj hw (Or.inr (Or.inr (Or.inl rfl)))
        (by rw [← hsz]; simp [translateTy, hk]; rfl)
      subst hw4
      have hrk' : rk = .char := hrk.trans hk
      subst hrk'
      dsimp only
      exact hchar hk
    · have hrk' : rk = .int it := hrk.trans hk
      subst hrk'; rfl
    · have hrk' : rk = .uint ut := hrk.trans hk
      subst hrk'; rfl

theorem validateLoadedValue_unionField_true {localDecls : List LocalDecl} {layouts : LayoutTable}
    {u : Local} {uDecl : LocalDecl} (hdecl_u : get? localDecls u = some uDecl)
    (isMove : Bool) (j : Nat) (fty : Ty) {bits w : Nat}
    (hbool : fty.kind = .bool → bits = 0 ∨ bits = 1) :
    validateLoadedValue layouts localDecls (unionFieldReadOperand isMove u j fty)
      (.scalar ⟨bits, w⟩) = true := by
  have hpt : placeTy localDecls layouts ⟨u, [.field j fty]⟩ = some fty := by
    simp [placeTy, hdecl_u, resolveProjectedTy]
  cases isMove <;>
    (simp only [unionFieldReadOperand, validateLoadedValue, operandTy, ↓reduceIte, Bool.false_eq_true];
     rw [hpt];
     dsimp only;
     by_cases hk : fty.kind = .bool
     · rw [hk]; rcases hbool hk with rfl | rfl <;> rfl
     · cases h : fty.kind <;> first | exact absurd h hk | rfl)

theorem validateLoadedValue_unionWhole_true {localDecls : List LocalDecl} {layouts : LayoutTable}
    {u : Local} {uDecl : LocalDecl} {S : Nat}
    (hdecl_u : get? localDecls u = some uDecl)
    (hwt : WellTypedUnionTy layouts uDecl.ty S)
    (isMove : Bool) (v : Value) :
    validateLoadedValue layouts localDecls
      (if isMove then .move ⟨u, .nil⟩ else .copy ⟨u, .nil⟩) v = true := by
  obtain ⟨defPath, args, _, _, hk, _, _, _, _, _, _, _, _, _, _, _⟩ := hwt.adt_spec
  have hpt : placeTy localDecls layouts ⟨u, .nil⟩ = some uDecl.ty := by
    simp [placeTy, hdecl_u, resolveProjectedTy]
  cases isMove <;>
    (simp only [validateLoadedValue, operandTy, ↓reduceIte, Bool.false_eq_true];
     rw [hpt];
     dsimp only;
     rw [hk])

/-- Anneal's `evalOperand` and `evalRvalue` on a union field read `copy/move u.j`
where `u` holds `unionSlotFields n f (.scalar sc)`:
1. Same field (`j = f`, `fty = f0Ty`): evaluates to `.scalar sc`.
2. Narrower/equal sibling field (`j ≠ f`, `w ≤ sc.sizeBytes`, bit-valid for `fty`):
   evaluates to the punned prefix `.scalar ⟨sc.bits % scalarModulus w, w⟩`.
3. Wider sibling field (`j ≠ f`, `sc.sizeBytes < w ≤ S`): fails with `.ub` because
   byte `sc.sizeBytes` in `[0, w)` is `.uninit`. -/
theorem evalOperand_unionFieldRead_spec
    {body : CapturedMir} {locals : List LocalSlot} {globals : List CapturedAllocation}
    {u j : Local} {fty : Ty} {isMove : Bool}
    {uDecl : LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    (hprim : IsPrimScalarTy fty) {w : Nat} (hw : ValidScalarBytes w)
    (hsz : (translateTy fty body.layouts).layout.size = translateSizeBytes w)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n) (hj : j < n)
    {f0Ty : Ty} {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hprim0 : IsPrimScalarTy f0Ty)
    (himm0 : ImmediateRel f0Ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)))
    (hk_le : sc.sizeBytes ≤ S)
    (hfl : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size)
    (hu_slot : get? locals u = some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))) :
    (j = f → fty = f0Ty →
      evalOperand locals (unionFieldReadOperand isMove u j fty) .nil globals body.layouts .nil
          body.localDecls = .ok (.scalar sc) locals) ∧
    (j ≠ f → w ≤ sc.sizeBytes →
      (fty.kind = .bool → sc.bits % scalarModulus w = 0 ∨ sc.bits % scalarModulus w = 1) →
      (fty.kind = .char → isValidCharCode (sc.bits % scalarModulus w) = true) →
      evalOperand locals (unionFieldReadOperand isMove u j fty) .nil globals body.layouts .nil
          body.localDecls = .ok (.scalar ⟨sc.bits % scalarModulus w, w⟩) locals) ∧
    (j ≠ f → sc.sizeBytes < w → w ≤ S →
      evalOperand locals (unionFieldReadOperand isMove u j fty) .nil globals body.layouts .nil
          body.localDecls = .ub) := by
  have htouch := placeTouchesUnion_union_field hdecl_u hwt j fty
  obtain ⟨defPath, args, tl, n', hk_u, _, _, hlookup, hfu, _, _, _, _, _, _, _⟩ := hwt.adt_spec
  have hn_eq : n' = n := by
    unfold translateTy at hfields
    dsimp only at hfields
    rw [hk_u, hlookup] at hfields
    dsimp only [translateTypeLayout, translateFieldsShape] at hfields
    rw [hfu] at hfields
    cases hfields; rfl
  simp only [hn_eq] at *
  have hr_base := resolveTyWithLocalDecls_of_union (localDecls := body.localDecls) hwt
  have hble_j : Nat.ble (j + 1) n = true := Nat.ble_eq.mpr hj
  have hcons := unionNeedsConsistencyCheck_unionSlotFields_scalar hf sc
  obtain ⟨rPt, hpt_eq, hpt_kind⟩ :=
    placeTyResolved_field_kind (layouts := body.layouts) hdecl_u j fty
  have hread_unfold : ∀ res,
      readProjectedValueUnionAware locals body.localDecls body.layouts
          (.aggregate 0 (unionSlotFields n f (.scalar sc))) uDecl.ty [.field j fty] = res →
      evalOperand locals (unionFieldReadOperand isMove u j fty) .nil globals body.layouts .nil
          body.localDecls =
        match res with
        | .ok fv =>
          if validateValueForTy? body.layouts (some rPt) fv then .ok fv locals else .ub
        | .ub => .ub
        | .unsupported => .unsupported := by
    intro res hres
    cases isMove <;>
      (simp only [unionFieldReadOperand, ↓reduceIte, Bool.false_eq_true];
       unfold evalOperand;
       dsimp only;
       rw [hu_slot]; dsimp only;
       rw [htouch]; dsimp only;
       (try (unfold readProjectedForLocal; rw [htouch]; dsimp only));
       rw [hdecl_u]; dsimp only;
       rw [hres, hpt_eq];
       cases res with
       | ok fv => dsimp only; cases validateValueForTy? body.layouts (some rPt) fv <;> rfl
       | ub => rfl
       | unsupported => rfl)
  refine ⟨fun hjf hfty => ?_, fun hjne hw_le hbool hchar => ?_, fun hjne hk_lt hw_le => ?_⟩
  · simp only [hjf, hfty] at *
    cases himm0 with
    | scalar _ _ hrel0 hsz0 hbool0 hchar0 =>
    have hvb0 : ValidScalarBytes sc.sizeBytes := hrel0.validBytes
    have hget := unionSlotFields_get_self hf (.scalar sc)
    have hrp : readProjectedValueUnionAware locals body.localDecls body.layouts
        (.aggregate 0 (unionSlotFields n f (.scalar sc))) uDecl.ty [.field f f0Ty] =
        .ok (.scalar sc) := by
      unfold readProjectedValueUnionAware
      dsimp only
      rw [hr_base, hk_u, hlookup]
      dsimp only
      rw [hfu]
      dsimp only
      rw [hble_j]; simp only []
      rw [hget, hcons]
      rfl
    have hval_ok : validateValueForTy? body.layouts (some rPt) (.scalar sc) = true := by
      cases sc with | mk bits szB =>
      exact validateValueForTy?_primScalar body.layouts hprim0 hvb0 hsz0
        (fun r hr => Option.some.inj hr ▸ hpt_kind)
        (fun hb => (hbool0 hb).2) (fun hc => (hchar0 hc).2)
    rw [hread_unfold _ hrp]
    dsimp only
    rw [hval_ok]; rfl
  · have hget := unionSlotFields_get_ne hf hj hjne (.scalar sc)
    have hw_pos : 0 < w := by rcases hw with rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨wPred, hw_succ⟩ : ∃ wPred, w = wPred + 1 := ⟨w - 1, by omega⟩
    have htySz : ∀ {rTy : Ty}, rTy.kind = fty.kind →
        tyByteSize body.localDecls body.layouts rTy = some (wPred + 1) := by
      intro rTy hrk
      rw [← hw_succ]
      exact tyByteSize_primScalar hprim hw hsz hrk
    have henc := encodeByLayoutIdxAux_unionSlotFields hwt hfields hf hprim0 himm0 hfl
    have hub_len : length (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
        replicateUninitBytes (S - sc.sizeBytes)) = S := by
      simp [encodeLittleEndianBytes_length, replicateUninitBytes_eq_replicate]; omega
    have hw_S : w ≤ S := Nat.le_trans hw_le hk_le
    have hslice : sliceAbstractBytes
        (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
          replicateUninitBytes (S - sc.sizeBytes)) 0 (wPred + 1) =
        some (encodeLittleEndianBytes sc.bits w none) := by
      rw [← hw_succ]
      unfold sliceAbstractBytes
      have hz0 : Nat.add 0 w = w := Nat.zero_add w
      rw [hz0, hub_len, Nat.ble_eq.mpr hw_S]
      dsimp only [dropAbstractBytes]
      rw [takeAbstractBytes_eq_take,
        List.take_append_of_le_length (by rw [encodeLittleEndianBytes_length]; exact hw_le),
        ← takeAbstractBytes_eq_take, takeAbstractBytes_encodeLittleEndianBytes w sc.sizeBytes _ _ hw_le]
    have hdec : ∀ {rTy : Ty}, rTy.kind = fty.kind →
        decodeTypedValueFromBytes defaultCodecFuel body.layouts rTy
          (encodeLittleEndianBytes sc.bits w none) =
          some (.scalar ⟨sc.bits % scalarModulus w, w⟩) := fun hrk =>
      decodeTypedValueFromBytes_primScalar hprim hw hsz hrk hbool hchar
    have hrp : readProjectedValueUnionAware locals body.localDecls body.layouts
        (.aggregate 0 (unionSlotFields n f (.scalar sc))) uDecl.ty [.field j fty] =
        .ok (.scalar ⟨sc.bits % scalarModulus w, w⟩) := by
      unfold readProjectedValueUnionAware
      dsimp only
      rw [hr_base, hk_u, hlookup]
      dsimp only
      rw [hfu]
      dsimp only
      rw [hble_j]; simp only []
      rw [hget, hcons]
      dsimp only
      cases hi : isUnresolvedLayoutIdx body.layouts fty.layoutIdx <;> dsimp only
      · have hts := htySz (rTy := fty) rfl
        have hd := hdec (rTy := fty) rfl
        rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
          (rw [hk]; dsimp only; rw [hts, henc]; dsimp only; rw [hslice]; dsimp only; rw [hd]; rfl)
      · cases hg : get? tl.fieldLayouts j <;> dsimp only
        · have hrk := resolveTyWithLocalDecls_kind_eq body.localDecls body.layouts fty
          have hts := htySz hrk
          have hd := hdec hrk
          rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
            (rw [hrk, hk]; dsimp only; rw [hts, henc]; dsimp only; rw [hslice]; dsimp only; rw [hd]; rfl)
        · rename_i flIdx
          rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
            (rw [hk]; dsimp only; rw [htySz hk.symm, henc]; dsimp only; rw [hslice]; dsimp only; rw [hdec hk.symm]; rfl)
    have hval_ok := validateValueForTy?_primScalar body.layouts hprim hw hsz
      (fun r hr => Option.some.inj hr ▸ hpt_kind) hbool hchar
    rw [hread_unfold _ hrp]
    dsimp only
    rw [hval_ok]; rfl
  · have hget := unionSlotFields_get_ne hf hj hjne (.scalar sc)
    have hvb0 : ValidScalarBytes sc.sizeBytes := by
      cases himm0 with | scalar _ _ hr _ _ _ => exact hr.validBytes
    have hk_pos : 1 ≤ sc.sizeBytes := by rcases hvb0 with h | h | h | h | h <;> omega
    have hw_ge2 : 2 ≤ w := by omega
    have hnot_bool : fty.kind ≠ .bool := by
      intro hb
      have hw1 : w = 1 := translateSizeBytes_inj hw (Or.inl rfl)
        (by rw [← hsz]; simp [translateTy, hb]; rfl)
      omega
    obtain ⟨wPred, hw_succ⟩ : ∃ wPred, w = wPred + 1 := ⟨w - 1, by omega⟩
    have htySz : ∀ {rTy : Ty}, rTy.kind = fty.kind →
        tyByteSize body.localDecls body.layouts rTy = some (wPred + 1) := by
      intro rTy hrk
      rw [← hw_succ]
      exact tyByteSize_primScalar hprim hw hsz hrk
    have henc := encodeByLayoutIdxAux_unionSlotFields hwt hfields hf hprim0 himm0 hfl
    have hub_len : length (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
        replicateUninitBytes (S - sc.sizeBytes)) = S := by
      simp [encodeLittleEndianBytes_length, replicateUninitBytes_eq_replicate]; omega
    have hrem_pos : 1 ≤ w - sc.sizeBytes := by omega
    have hslice : sliceAbstractBytes
        (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
          replicateUninitBytes (S - sc.sizeBytes)) 0 (wPred + 1) =
        some (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
          .uninit :: List.replicate (w - sc.sizeBytes - 1) .uninit) := by
      rw [← hw_succ]
      unfold sliceAbstractBytes
      have hz0 : Nat.add 0 w = w := Nat.zero_add w
      rw [hz0, hub_len, Nat.ble_eq.mpr hw_le]
      dsimp only [dropAbstractBytes]
      rw [takeAbstractBytes_eq_take, replicateUninitBytes_eq_replicate,
        List.take_append, encodeLittleEndianBytes_length,
        List.take_of_length_le (by rw [encodeLittleEndianBytes_length]; omega),
        List.take_replicate, Nat.min_eq_left (by omega)]
      have hrep : List.replicate (w - sc.sizeBytes) AbstractByte.uninit =
          .uninit :: List.replicate (w - sc.sizeBytes - 1) .uninit := by
        conv => lhs; rw [show w - sc.sizeBytes = (w - sc.sizeBytes - 1) + 1 by omega]
        rfl
      rw [hrep]
    have hdec : ∀ {rTy : Ty}, rTy.kind = fty.kind →
        decodeTypedValueFromBytes defaultCodecFuel body.layouts rTy
          (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
            AbstractByte.uninit :: List.replicate (w - sc.sizeBytes - 1) AbstractByte.uninit) = none := fun hrk =>
      decodeTypedValueFromBytes_primScalar_uninit (layouts := body.layouts)
        hprim hrk (encodeLittleEndianBytes sc.bits sc.sizeBytes none)
        (List.replicate (w - sc.sizeBytes - 1) AbstractByte.uninit) hnot_bool
    have hrp : readProjectedValueUnionAware locals body.localDecls body.layouts
        (.aggregate 0 (unionSlotFields n f (.scalar sc))) uDecl.ty [.field j fty] = .ub := by
      unfold readProjectedValueUnionAware
      dsimp only
      rw [hr_base, hk_u, hlookup]
      dsimp only
      rw [hfu]
      dsimp only
      rw [hble_j]; simp only []
      rw [hget, hcons]
      dsimp only
      cases hi : isUnresolvedLayoutIdx body.layouts fty.layoutIdx <;> dsimp only
      · have hts := htySz (rTy := fty) rfl
        have hd := hdec (rTy := fty) rfl
        rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
          (rw [hk]; dsimp only; rw [hts, henc]; dsimp only; rw [hslice]; dsimp only; rw [hd])
      · cases hg : get? tl.fieldLayouts j <;> dsimp only
        · have hrk := resolveTyWithLocalDecls_kind_eq body.localDecls body.layouts fty
          have hts := htySz hrk
          have hd := hdec hrk
          rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
            (rw [hrk, hk]; dsimp only; rw [hts, henc]; dsimp only; rw [hslice]; dsimp only; rw [hd])
        · rename_i flIdx
          rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
            (rw [hk]; dsimp only; rw [htySz hk.symm, henc]; dsimp only; rw [hslice]; dsimp only; rw [hdec hk.symm])
    rw [hread_unfold _ hrp]

/-- **`step_union_field_read_simulation`** and
**`union_uninit_bytes_read_ub_simulation`** (`LM-2.4`): reading field `j` of a
union that holds active field `f`'s (`f < n`) value `sc` (`k = sc.sizeBytes`
initialized bytes of `S`), with `_r = copy u.j` or `_r = move u.j`:

1. Reading the active field `j = f` (`fty = f0Ty`) steps both machines to related
   states in which `_r` holds `sc`.
2. Reading a sibling field `j ≠ f` of `w` bytes with `k < w ≤ S`, whose bytes
   `[0, w)` include the uninitialized byte `k`, is undefined behavior in both
   machines: Anneal's byte-reinterpreting union read hits `.uninit` in
   `decodeTypedValueFromBytes`, and `lean-miri`'s `Allocation.readScalar` finds
   the uninitialized byte in `InitMask`. -/
theorem step_union_field_read_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {r u j : Local} {fty : Ty} {isMove : Bool} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩)
    {rDecl uDecl : LocalDecl}
    (hdecl_r : get? body.localDecls r = some rDecl) (hr_ty : rDecl.ty = fty)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hprim : IsPrimScalarTy fty) {w : Nat} (hw : ValidScalarBytes w)
    (hsz : (translateTy fty body.layouts).layout.size = translateSizeBytes w)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n) (hj : j < n)
    {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hr_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame r)
    (hfl : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size := by exact ⟨_, rfl, rfl⟩) :
    (j = f → fty = f0Ty →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
      (∀ s', stepMirFn body s = .step s' →
        get? s'.frame.locals r = some (.init (.scalar sc))) ∧
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m).1.machine =
        m.machine) ∧
    (j ≠ f → sc.sizeBytes < w → w ≤ S →
      stepMirFn body s = .fail .ub ∧
      ∃ m' msg,
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .error (.undefinedBehavior msg))) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem; dsimp only at hbor hprot; subst hbor hprot; rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩
      body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
  obtain ⟨c_u, hmls_u⟩ := hu_mls topFrame hframes
  obtain ⟨_, mls_r0, _, hlt_r0, _, _, hmls_r_eq, hloc_r0⟩ := hframe.lookup_local hdecl_r
  have hr_imm0 := hr_imm topFrame hframes
  obtain ⟨_, mls_u0, _, hlt_u0, _, hmls_u0, _, hloc_u0⟩ := hframe.lookup_local hdecl_u
  have hmls_u0' : mls_u0 = ⟨.live (.indirect mp), c_u⟩ := by
    rw [hmls_u] at hmls_u0; exact (Option.some.inj hmls_u0).symm
  have hru : r ≠ u := fun hru => by subst hru; exact hr_imm0 _ hmls_u mp rfl
  let topFrame₀ :=
    cacheFrameLocalLayout topFrame r hlt_r0 (translateTy rDecl.ty body.layouts)
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 r none topFrame.localsIdentity, translateTy rDecl.ty body.layouts⟩
  have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨r, #[]⟩ m =
      .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_r0 hdecl_r
      (by rw [hmls_r_eq]; exact hloc_r0.layout_eq)
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀, cacheFrameLocalLayout]; rw [Array.size_set]; exact hlt_u0
  have hu₀' : topFrame₀.locals[u]? = some ⟨.live (.indirect mp), c_u⟩ := by
    dsimp only [topFrame₀, cacheFrameLocalLayout]
    rw [Array.getElem?_set_ne _ hru]; exact hmls_u
  have hu₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp), c_u⟩ := by
    have h := Array.getElem?_eq_getElem hlt_u₀
    rw [hu₀'] at h; exact (Option.some.inj h).symm
  have hcache_u : ∀ l, (topFrame₀.locals[u]'hlt_u₀).layout = some l →
      l = translateTy uDecl.ty body.layouts := by
    rw [hu₀]; rw [hmls_u0'] at hloc_u0; exact hloc_u0.layout_eq
  obtain ⟨msc0, hmeta, hk_le0, hprim0, himm0⟩ :
      ∃ msc0, mp.metadata = .none ∧ sc.sizeBytes ≤ S ∧ IsPrimScalarTy f0Ty ∧
        ImmediateRel f0Ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc0)) := by
    cases hmem with
    | mk _ _ _ _ msc0 _ _ hm _ _ _ _ _ _ _ _ _ _ _ hkle _ _ hp0 hi0 _ =>
      exact ⟨msc0, hm, hkle, hp0, hi0⟩
  have hop_spec := evalOperand_unionFieldRead_spec (globals := s.memory.globals) (isMove := isMove)
    hdecl_u hprim hw hsz hwt hfields hf hj hprim0 himm0 hk_le0 hfl hu_slot
  let topFrame₁ :=
    cacheFrameLocalLayout topFrame₀ u hlt_u₀ (translateTy uDecl.ty body.layouts)
  let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
  have hop : annealEvalOperandLM2_4 body.localDecls body.layouts
      (translateOperand (unionFieldReadOperand isMove u j fty))
      (some (translateTy rDecl.ty body.layouts)) m₀ =
      .ok ⟨.indirect mp, translateTy fty body.layouts⟩ m₁ := by
    have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
    have hfield := annealEvalUnionField_indirect (body := body) (m := m₀) rfl hlt_u₀ hdecl_u
      hcache_u (by rw [hu₀]) hmeta hfields hj hprim
    cases isMove <;>
      simp only [unionFieldReadOperand, translateOperand, translatePlace, List.map,
        translateProjectionElem, List.toArray, annealEvalOperandLM2_4, hunion, ↓reduceIte,
        Bool.false_eq_true] <;>
      exact hfield
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨r, #[]⟩
      (translateRvalue (.use (unionFieldReadOperand isMove u j fty))) = true := by
    have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
    cases isMove <;>
      simp [lm24Assign, lm24Rvalue, lm24Operand, lm24Place, translateRvalue, translateOperand,
        unionFieldReadOperand, translatePlace, hunion]
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩) m =
      Miri.Interpreter.runRvalue
        ((annealReadImmediateLM2_2 ⟨.indirect mp, translateTy fty body.layouts⟩ >>=
          fun imm => annealWriteImmediateLM2_2 imm.imm destPlace)) m₁ := by
    have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
        ⟨r, #[]⟩ true m = .ok destPlace m₀ := hevalPlace_dst
    have hop' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
        (Miri.Interpreter.OperandPath.rvalue "operand")
        (translateOperand (unionFieldReadOperand isMove u j fty))
        (some ((annealRvalueHooksLM2_4 body.localDecls body.layouts).placeLayout destPlace)) m₀ =
        .ok ⟨.indirect mp, translateTy fty body.layouts⟩ m₁ := hop
    have huse : usesMemCopy ⟨.indirect mp, translateTy fty body.layouts⟩ = false := by
      simp [usesMemCopy, hprim.fields_primitive]
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace']
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop']
    simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2, huse, Bool.false_eq_true, ↓reduceIte]
  have hframe₁ : FrameRelLM2_4 body m.machine s.frame topFrame₁ :=
    (hframe.cache_local_layout hdecl_r hlt_r0).cache_local_layout hdecl_u hlt_u₀
  have hdisj₁ : MemoryAllocDisjoint topFrame₁ :=
    (hdisj.cache_layout hlt_r0 _).cache_layout hlt_u₀ _
  have hr_imm₁ : IsImmediateFrameLocal topFrame₁ r :=
    (hr_imm0.cache_layout hlt_r0 _).cache_layout hlt_u₀ _
  have hretCont₁ : topFrame₁.returnContinuation = .stop false := hretCont
  have hretPlace₁ : ∃ retLay, topFrame₁.returnPlace =
      .frameLocal 0 0 none retLay topFrame₁.localsIdentity := ⟨retLay, hretPlace⟩
  obtain ⟨hsame, hbig⟩ := annealReadImmediate_unionMem (m := m₁) hnodup hwt.size_valid hmem
    hprim hw hsz
  obtain ⟨hf0sz, hkv⟩ := hmem.f0_size
  refine ⟨fun hjf hty => ?_, fun hjne hlt hwS => ?_⟩
  · have hop_ok := hop_spec.1 hjf hty
    simp only [hjf, hty] at *
    have hwk : w = sc.sizeBytes :=
      translateSizeBytes_inj hw hkv (hsz.symm.trans hf0sz)
    obtain ⟨msc, _, himm, hread⟩ := hsame hwk
    cases himm0 with
    | scalar _ _ _ _ hbool0 _ =>
    have hval_ld : validateLoadedValue body.layouts body.localDecls
        (unionFieldReadOperand isMove u f f0Ty) (.scalar sc) = true := by
      cases sc with | mk bits szB =>
      exact validateLoadedValue_unionField_true hdecl_u isMove f f0Ty (fun hb => (hbool0 hb).2)
    have hrv_ok : evalRvalue s.frame.locals (.use (unionFieldReadOperand isMove u f f0Ty)) s.memory
        body.localDecls body.layouts = .ok (.scalar sc) s.frame.locals s.memory := by
      unfold evalRvalue; dsimp only
      rw [hbor, hcaller, hop_ok]; dsimp only; rw [hval_ld]
      cases isMove <;> rfl
    have ha_ok : evalStmt s
        ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u f f0Ty)), span⟩
        body.localDecls body.layouts =
        match get? s.frame.locals r with
        | .some .dead => MirStepNode.fail .ub
        | .some _ =>
          match set? s.frame.locals r (.init (.scalar sc)) with
          | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
          | .none => MirStepNode.fail .ub
        | .none => MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only; rw [hrv_ok]; simp only []
      rw [hprot, hbor]; dsimp only [invalidateConflictingBorrows]; rw [hmem_same]
      cases get? s.frame.locals r with
      | none => rfl
      | some sl => cases sl <;> (try rfl) <;> cases set? s.frame.locals r (.init (.scalar sc)) <;> rfl
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u f f0Ty)), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc)) destPlace) m₁ := by
      rw [hm_eval]
      apply runRvalue_eq_of_eq
      exact EStateM.bind_eq_ok hread
    have himm_r : ImmediateRel rDecl.ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)) := by
      rw [hr_ty]; exact himm
    have hext := write_after_rvalue_simulation_LM2_4
      (annealStepHooksLM2_4 body.localDecls body.layouts)
      hretCont₁ hretPlace₁ hcal hstack hbor hprot hcaller hframes hframe.body_eq
      hframe.location_eq hbb hstmt hframe₁ hdisj₁ hdecl_r hr_imm₁ himm_r ha_ok hm_write
    rw [hstep_a]
    refine ⟨hext.1, ?_, hext.2.1⟩
    intro s' hs'
    rw [ha_ok] at hs'
    obtain ⟨_, _, hlt_af, _, hslot_r, _, _, _⟩ := hframe.lookup_local hdecl_r
    rw [hslot_r] at hs'
    split at hs'
    · exact absurd hs' MirStepNode_fail_ne_step
    · rw [set?_eq_some_set hlt_af] at hs'
      have hs'' := MirStepNode_step_inj hs'
      subst hs''
      simp [advanceStmt, get?_eq_getElem?, hlt_af]
    · exact absurd hs' MirStepNode_fail_ne_step
  · have hop_ub := hop_spec.2.2 hjne hlt hwS
    have ha_ub : evalStmt s
        ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue; dsimp only; rw [hbor, hcaller, hop_ub]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩) m =
        (m₁, .error (.undefinedBehavior "read of uninitialized memory field")) := by
      rw [hm_eval]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error (hbig hlt hwS)]
    exact ⟨by rw [hstep_a, ha_ub], m₁, _,
      miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err⟩

private theorem writeAbstractBytesAt_zero_eq :
    ∀ (buf patch : List AbstractByte),
      patch.length ≤ buf.length →
      writeAbstractBytesAt buf 0 patch = some (patch ++ buf.drop patch.length)
  | buf, [], _ => by cases buf <;> simp [writeAbstractBytesAt]
  | [], _ :: _, h => absurd h (by simp)
  | _ :: bs, p :: ps, h => by
    unfold writeAbstractBytesAt
    rw [writeAbstractBytesAt_zero_eq bs ps (Nat.le_of_succ_le_succ h)]
    simp

private theorem rebuildUnionFieldsAfterWriteOpt_scalar_aux (layouts : LayoutTable)
    (j : Nat) (sc' : MirAst.ScalarInt) :
    ∀ (rem curIdx : Nat) (flIdxs : List Nat) (oldFields : List Value),
      (∀ v ∈ oldFields, v = .unit ∨ ∃ s, v = .scalar s) →
      rebuildUnionFieldsAfterWriteOpt layouts j curIdx (.scalar sc') rem flIdxs oldFields =
        some ((List.range' curIdx rem).map (fun i => if i = j then .scalar sc' else .unit))
  | 0, _, _, _, _ => rfl
  | rem + 1, curIdx, flIdxs, oldFields, hold => by
    have hold_next : ∀ v ∈ (match oldFields with | _ :: r => r | [] => []),
        v = .unit ∨ ∃ s, v = .scalar s := by
      cases oldFields with
      | nil => intro _ h; nomatch h
      | cons v vs => intro v' hv'; exact hold v' (List.mem_cons_of_mem _ hv')
    have hih := rebuildUnionFieldsAfterWriteOpt_scalar_aux layouts j sc' rem (curIdx + 1)
      (match flIdxs with | _ :: r => r | [] => [])
      (match oldFields with | _ :: r => r | [] => []) hold_next
    unfold rebuildUnionFieldsAfterWriteOpt
    cases flIdxs <;> cases oldFields <;>
      (dsimp only at hih ⊢;
       rw [show curIdx.succ = curIdx + 1 from rfl, hih];
       dsimp only [List.range', List.map];
       by_cases hcj : curIdx = j
       · subst hcj; simp
       · have hbeq : Nat.beq curIdx j = false := by
           cases h : Nat.beq curIdx j with
           | false => rfl
           | true => exact absurd (Nat.eq_of_beq_eq_true h) hcj
         simp only [hbeq, hcj, ↓reduceIte]
         try (rcases hold _ List.mem_cons_self with rfl | ⟨s, rfl⟩ <;> rfl))

private theorem range'_map_ite_eq_unionSlotFields {n j : Nat} (hj : j < n) (v : Value) :
    (List.range' 0 n).map (fun i => if i = j then v else .unit) = unionSlotFields n j v := by
  rw [unionSlotFields_eq_list]
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map, List.getElem?_append, List.length_replicate,
    List.getElem?_replicate, List.getElem?_cons]
  by_cases hi : i < n
  · have hr : (List.range' 0 n)[i]? = some i := by
      rw [List.getElem?_eq_getElem (by simp [hi]), List.getElem_range']
      simp
    rw [hr]
    dsimp only [Option.map]
    by_cases hij : i = j
    · subst hij
      have h1 : ¬ (i < i) := Nat.lt_irrefl i
      simp [h1]
    · rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
      · simp [hij, hlt]
      · have h1 : ¬ (i < j) := by omega
        obtain ⟨d, hd⟩ : ∃ d, i - j = d + 1 := ⟨i - j - 1, by omega⟩
        have hd_lt : d < n - (j + 1) := by omega
        simp [hij, h1, hd, hd_lt]
  · have hr : (List.range' 0 n)[i]? = none :=
      List.getElem?_eq_none (by simp; omega)
    rw [hr]
    have h1 : ¬ (i < j) := by omega
    have h0 : i - j ≠ 0 := by omega
    have h2 : ¬ (i - j - 1 < n - (j + 1)) := by omega
    simp [h1, h0, h2]

theorem writeProjectedForLocal_union_field_uninit {body : CapturedMir} {locals : List LocalSlot}
    {u j : Local} {fty : Ty} {uDecl : LocalDecl}
    (hdecl_u : get? body.localDecls u = some uDecl)
    {S n : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hj : j < n)
    {sc' : MirAst.ScalarInt} {msc' : Miri.Memory.ScalarInt}
    (hprim : IsPrimScalarTy fty)
    (himm' : ImmediateRel fty body.layouts (.scalar sc') (.scalar (.fromScalarInt msc')))
    (hk'_le : sc'.sizeBytes ≤ S)
    (hfl : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) j = some fl ∧
      fl.layout.size = (translateTy fty body.layouts).layout.size) :
    uninitFieldWriteShell? body.localDecls body.layouts u (.field j fty) .nil =
      some (.aggregate 0 .nil) ∧
    writeProjectedForLocal locals body.localDecls body.layouts u (.aggregate 0 .nil)
        [.field j fty] (.scalar sc') =
      .ok (.aggregate 0 (unionSlotFields n j (.scalar sc'))) := by
  obtain ⟨defPath, args, tl, n', hk_u, _, _, hlookup, hfu, _, _, htl_sz, _, _, _, _⟩ :=
    hwt.adt_spec
  have hn_eq : n' = n := by
    unfold translateTy at hfields
    dsimp only at hfields
    rw [hk_u, hlookup] at hfields
    dsimp only [translateTypeLayout, translateFieldsShape] at hfields
    rw [hfu] at hfields; cases hfields; rfl
  simp only [hn_eq] at *
  have hshell : uninitFieldWriteShell? body.localDecls body.layouts u (.field j fty) .nil =
      some (.aggregate 0 .nil) := by
    unfold uninitFieldWriteShell? placeTy
    rw [hdecl_u]
    dsimp only [resolveProjectedTy]
    cases hty_u : uDecl.ty with | mk uk ul =>
    rw [hty_u] at hk_u
    dsimp only at hk_u ⊢
    subst hk_u
    rfl
  refine ⟨hshell, ?_⟩
  have htouch := placeTouchesUnion_union_field hdecl_u hwt j fty
  have hr_base := resolveTyWithLocalDecls_of_union (localDecls := body.localDecls) hwt
  have hble_j : Nat.ble (j + 1) n = true := Nat.ble_eq.mpr hj
  have hbase_enc := encodeByLayoutIdxAux_union_nil hwt
  have hcons_nil : unionNeedsConsistencyCheck n [] = false := by
    unfold unionNeedsConsistencyCheck unionNonUnitTypedSlotCount
    cases n <;> rfl
  have hwrite_at : writeAbstractBytesAt (replicateUninitBytes S) 0
      (encodeLittleEndianBytes sc'.bits sc'.sizeBytes none) =
      some (encodeLittleEndianBytes sc'.bits sc'.sizeBytes none ++
        replicateUninitBytes (S - sc'.sizeBytes)) := by
    rw [writeAbstractBytesAt_zero_eq _ _
      (by rw [encodeLittleEndianBytes_length, replicateUninitBytes_eq_replicate, List.length_replicate]; exact hk'_le)]
    simp [encodeLittleEndianBytes_length, replicateUninitBytes_eq_replicate, List.drop_replicate]
  have hrebuild : rebuildUnionFieldsAfterWriteOpt body.layouts j 0 (.scalar sc') n tl.fieldLayouts [] =
      some (unionSlotFields n j (.scalar sc')) := by
    rw [rebuildUnionFieldsAfterWriteOpt_scalar_aux _ _ _ _ _ _ _
      (fun _ h => False.elim (List.not_mem_nil h)),
      range'_map_ite_eq_unionSlotFields hj]
  have hre_enc := encodeByLayoutIdxAux_unionSlotFields hwt hfields hj hprim himm' hfl
  have hfin : finalizeUnionFieldsWithRawOverlayOpt body.layouts uDecl.ty.layoutIdx
      (unionSlotFields n j (.scalar sc'))
      (encodeLittleEndianBytes sc'.bits sc'.sizeBytes none ++
        replicateUninitBytes (S - sc'.sizeBytes)) =
      some (unionSlotFields n j (.scalar sc')) := by
    unfold finalizeUnionFieldsWithRawOverlayOpt
    rw [hre_enc]
    dsimp only
    rw [abstractByteListEq_refl]
    dsimp only
    rw [forceValueListOpt_eq_some]
  unfold writeProjectedForLocal
  rw [htouch, hdecl_u]
  dsimp only
  unfold writeProjectedValueUnionAware
  dsimp only
  rw [hr_base, hk_u, hlookup]
  dsimp only
  rw [hfu]
  dsimp only
  rw [hble_j]; simp only []
  rw [hbase_enc, hcons_nil]
  simp only [Bool.true_or, unionActiveSlotIsZstPlaceholder]
  rw [encodeTypedValueToBytes_primScalar hprim himm' (by
    cases isUnresolvedLayoutIdx body.layouts fty.layoutIdx
    · rfl
    · cases get? tl.fieldLayouts j
      · exact resolveTyWithLocalDecls_kind_eq body.localDecls body.layouts fty
      · rfl)]
  dsimp only
  simp only [unionSlotLacksLayoutFreeImage]
  rw [hwrite_at, hrebuild]
  dsimp only
  rw [hfin]

theorem writeProjectedForLocal_union_field_ge {body : CapturedMir} {locals : List LocalSlot}
    {u j : Local} {fty : Ty} {uDecl : LocalDecl}
    (hdecl_u : get? body.localDecls u = some uDecl)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n) (hj : j < n)
    {f0Ty : Ty} {sc sc' : MirAst.ScalarInt} {msc msc' : Miri.Memory.ScalarInt}
    (hprim0 : IsPrimScalarTy f0Ty)
    (himm0 : ImmediateRel f0Ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)))
    (hfl0 : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size)
    (hprim : IsPrimScalarTy fty)
    (himm' : ImmediateRel fty body.layouts (.scalar sc') (.scalar (.fromScalarInt msc')))
    (hk_ge : sc.sizeBytes ≤ sc'.sizeBytes)
    (hk'_le : sc'.sizeBytes ≤ S)
    (hfl' : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) j = some fl ∧
      fl.layout.size = (translateTy fty body.layouts).layout.size) :
    writeProjectedForLocal locals body.localDecls body.layouts u
        (ensureNestedFieldShells (.aggregate 0 (unionSlotFields n f (.scalar sc))) [.field j fty])
        [.field j fty] (.scalar sc') =
      .ok (.aggregate 0 (unionSlotFields n j (.scalar sc'))) := by
  dsimp only [ensureNestedFieldShells]
  obtain ⟨defPath, args, tl, n', hk_u, _, _, hlookup, hfu, _, _, htl_sz, _, _, _, _⟩ :=
    hwt.adt_spec
  have hn_eq : n' = n := by
    unfold translateTy at hfields
    dsimp only at hfields
    rw [hk_u, hlookup] at hfields
    dsimp only [translateTypeLayout, translateFieldsShape] at hfields
    rw [hfu] at hfields; cases hfields; rfl
  simp only [hn_eq] at *
  have htouch := placeTouchesUnion_union_field hdecl_u hwt j fty
  have hr_base := resolveTyWithLocalDecls_of_union (localDecls := body.localDecls) hwt
  have hble_j : Nat.ble (j + 1) n = true := Nat.ble_eq.mpr hj
  have hbase_enc := encodeByLayoutIdxAux_unionSlotFields hwt hfields hf hprim0 himm0 hfl0
  have hcons := unionNeedsConsistencyCheck_unionSlotFields_scalar hf sc
  have hk_le : sc.sizeBytes ≤ S := Nat.le_trans hk_ge hk'_le
  have hwrite_at : writeAbstractBytesAt
      (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
        replicateUninitBytes (S - sc.sizeBytes)) 0
      (encodeLittleEndianBytes sc'.bits sc'.sizeBytes none) =
      some (encodeLittleEndianBytes sc'.bits sc'.sizeBytes none ++
        replicateUninitBytes (S - sc'.sizeBytes)) := by
    rw [writeAbstractBytesAt_zero_eq _ _ (by
      simp [encodeLittleEndianBytes_length, replicateUninitBytes_eq_replicate]; omega)]
    rw [encodeLittleEndianBytes_length, List.drop_append,
      List.drop_of_length_le (by rw [encodeLittleEndianBytes_length]; exact hk_ge),
      encodeLittleEndianBytes_length, List.nil_append,
      replicateUninitBytes_eq_replicate, List.drop_replicate,
      show S - sc.sizeBytes - (sc'.sizeBytes - sc.sizeBytes) = S - sc'.sizeBytes by omega,
      ← replicateUninitBytes_eq_replicate]
  have hold_mem : ∀ v ∈ unionSlotFields n f (.scalar sc), v = .unit ∨ ∃ s, v = .scalar s := by
    rw [unionSlotFields_eq_list]
    intro v hv
    rcases List.mem_append.mp hv with h1 | h2
    · exact Or.inl (List.eq_of_mem_replicate h1)
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact Or.inr ⟨sc, rfl⟩
      · exact Or.inl (List.eq_of_mem_replicate h3)
  have hrebuild : rebuildUnionFieldsAfterWriteOpt body.layouts j 0 (.scalar sc') n tl.fieldLayouts
      (unionSlotFields n f (.scalar sc)) =
      some (unionSlotFields n j (.scalar sc')) := by
    rw [rebuildUnionFieldsAfterWriteOpt_scalar_aux _ _ _ _ _ _ _ hold_mem,
      range'_map_ite_eq_unionSlotFields hj]
  have hre_enc := encodeByLayoutIdxAux_unionSlotFields hwt hfields hj hprim himm' hfl'
  have hfin : finalizeUnionFieldsWithRawOverlayOpt body.layouts uDecl.ty.layoutIdx
      (unionSlotFields n j (.scalar sc'))
      (encodeLittleEndianBytes sc'.bits sc'.sizeBytes none ++
        replicateUninitBytes (S - sc'.sizeBytes)) =
      some (unionSlotFields n j (.scalar sc')) := by
    unfold finalizeUnionFieldsWithRawOverlayOpt
    rw [hre_enc]
    dsimp only
    rw [abstractByteListEq_refl]
    dsimp only
    rw [forceValueListOpt_eq_some]
  unfold writeProjectedForLocal
  rw [htouch, hdecl_u]
  dsimp only
  unfold writeProjectedValueUnionAware
  dsimp only
  rw [hr_base, hk_u, hlookup]
  dsimp only
  rw [hfu]
  dsimp only
  rw [hble_j]; simp only []
  rw [hbase_enc, hcons]
  simp only [Bool.true_or, unionActiveSlotIsZstPlaceholder]
  rw [encodeTypedValueToBytes_primScalar hprim himm' (by
    cases isUnresolvedLayoutIdx body.layouts fty.layoutIdx
    · rfl
    · cases get? tl.fieldLayouts j
      · exact resolveTyWithLocalDecls_kind_eq body.localDecls body.layouts fty
      · rfl)]
  dsimp only
  simp only [unionSlotLacksLayoutFreeImage]
  rw [hwrite_at, hrebuild]
  dsimp only
  rw [hfin]

private theorem abstractByteListEq_append_same_prefix :
    ∀ (pfx xs ys : List AbstractByte),
      abstractByteListEq (pfx ++ xs) (pfx ++ ys) = abstractByteListEq xs ys
  | [], _, _ => rfl
  | b :: pfx, xs, ys => by
    simp [abstractByteListEq, abstractByteEq_refl b,
      abstractByteListEq_append_same_prefix pfx xs ys]

private theorem drop_encodeLittleEndianBytes_nonempty :
    ∀ (w k x : Nat) (p : Option (Nat × Nat)), w < k →
      ∃ b p' tail, (encodeLittleEndianBytes x k p).drop w = .init b p' :: tail
  | 0, _ + 1, x, p, _ => ⟨UInt8.ofNat x, p, _, rfl⟩
  | _ + 1, 0, _, _, h => absurd h (by omega)
  | w + 1, k + 1, x, p, h =>
    drop_encodeLittleEndianBytes_nonempty w k (Nat.div x 256) p (Nat.lt_of_succ_lt_succ h)

/-- Projected write of a *narrower* scalar field `_u.j = sc'` (`sc'.sizeBytes < sc.sizeBytes ≤ S`)
on an initialized `n`-field union `_u` holding `unionSlotFields n f (.scalar sc)`:
`writeProjectedValueUnionAware` splices `sc'`'s low bytes over `sc`'s byte image and,
because the retained high bytes `[sc'.sizeBytes, sc.sizeBytes)` are initialized while
the single-slot image of `sc'` leaves `[sc'.sizeBytes, S)` `.uninit`
(`abstractByteListEq = false`), `finalizeUnionFieldsWithRawOverlayOpt` attaches the
raw-byte overlay `.aggregate 0 (encodeRawAbstractByteVals mergedBytes)` (`D13a`). -/
theorem writeProjectedForLocal_union_field_lt {body : CapturedMir} {locals : List LocalSlot}
    {u j : Local} {fty : Ty} {uDecl : LocalDecl}
    (hdecl_u : get? body.localDecls u = some uDecl)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n) (hj : j < n)
    {f0Ty : Ty} {sc sc' : MirAst.ScalarInt} {msc msc' : Miri.Memory.ScalarInt}
    (hprim0 : IsPrimScalarTy f0Ty)
    (himm0 : ImmediateRel f0Ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)))
    (hfl0 : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size)
    (hprim : IsPrimScalarTy fty)
    (himm' : ImmediateRel fty body.layouts (.scalar sc') (.scalar (.fromScalarInt msc')))
    (hk_lt : sc'.sizeBytes < sc.sizeBytes)
    (hk_le : sc.sizeBytes ≤ S)
    (hfl' : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) j = some fl ∧
      fl.layout.size = (translateTy fty body.layouts).layout.size) :
    let mergedBytes :=
      encodeLittleEndianBytes sc'.bits sc'.sizeBytes none ++
        ((encodeLittleEndianBytes sc.bits sc.sizeBytes none).drop sc'.sizeBytes ++
          replicateUninitBytes (S - sc.sizeBytes))
    writeProjectedForLocal locals body.localDecls body.layouts u
        (ensureNestedFieldShells (.aggregate 0 (unionSlotFields n f (.scalar sc))) [.field j fty])
        [.field j fty] (.scalar sc') =
      .ok (.aggregate 0
        (unionSlotFields n j (.scalar sc') ++
          [.aggregate 0 (encodeRawAbstractByteVals mergedBytes)])) := by
  intro mergedBytes
  dsimp only [ensureNestedFieldShells]
  obtain ⟨defPath, args, tl, n', hk_u, _, _, hlookup, hfu, _, _, htl_sz, _, _, _, _⟩ :=
    hwt.adt_spec
  have hn_eq : n' = n := by
    unfold translateTy at hfields
    dsimp only at hfields
    rw [hk_u, hlookup] at hfields
    dsimp only [translateTypeLayout, translateFieldsShape] at hfields
    rw [hfu] at hfields; cases hfields; rfl
  simp only [hn_eq] at *
  have htouch := placeTouchesUnion_union_field hdecl_u hwt j fty
  have hr_base := resolveTyWithLocalDecls_of_union (localDecls := body.localDecls) hwt
  have hble_j : Nat.ble (j + 1) n = true := Nat.ble_eq.mpr hj
  have hbase_enc := encodeByLayoutIdxAux_unionSlotFields hwt hfields hf hprim0 himm0 hfl0
  have hcons := unionNeedsConsistencyCheck_unionSlotFields_scalar hf sc
  have hwrite_at : writeAbstractBytesAt
      (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
        replicateUninitBytes (S - sc.sizeBytes)) 0
      (encodeLittleEndianBytes sc'.bits sc'.sizeBytes none) =
      some mergedBytes := by
    rw [writeAbstractBytesAt_zero_eq _ _ (by
      simp [encodeLittleEndianBytes_length, replicateUninitBytes_eq_replicate]; omega)]
    rw [encodeLittleEndianBytes_length,
      List.drop_append_of_le_length (by rw [encodeLittleEndianBytes_length]; omega)]
  have hold_mem : ∀ v ∈ unionSlotFields n f (.scalar sc), v = .unit ∨ ∃ s, v = .scalar s := by
    rw [unionSlotFields_eq_list]
    intro v hv
    rcases List.mem_append.mp hv with h1 | h2
    · exact Or.inl (List.eq_of_mem_replicate h1)
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact Or.inr ⟨sc, rfl⟩
      · exact Or.inl (List.eq_of_mem_replicate h3)
  have hrebuild : rebuildUnionFieldsAfterWriteOpt body.layouts j 0 (.scalar sc') n tl.fieldLayouts
      (unionSlotFields n f (.scalar sc)) =
      some (unionSlotFields n j (.scalar sc')) := by
    rw [rebuildUnionFieldsAfterWriteOpt_scalar_aux _ _ _ _ _ _ _ hold_mem,
      range'_map_ite_eq_unionSlotFields hj]
  have hre_enc := encodeByLayoutIdxAux_unionSlotFields hwt hfields hj hprim himm' hfl'
  have hneq_bytes :
      abstractByteListEq
        (encodeLittleEndianBytes sc'.bits sc'.sizeBytes none ++
          replicateUninitBytes (S - sc'.sizeBytes))
        mergedBytes = false := by
    dsimp only [mergedBytes]
    rw [abstractByteListEq_append_same_prefix]
    obtain ⟨b, p', tail, hdrop⟩ :=
      drop_encodeLittleEndianBytes_nonempty sc'.sizeBytes sc.sizeBytes sc.bits none hk_lt
    have hpos : S - sc'.sizeBytes = (S - sc'.sizeBytes - 1) + 1 := by omega
    rw [hpos, replicateUninitBytes_eq_replicate, List.replicate_succ, hdrop]
    rfl
  have hfin : finalizeUnionFieldsWithRawOverlayOpt body.layouts uDecl.ty.layoutIdx
      (unionSlotFields n j (.scalar sc')) mergedBytes =
      some (unionSlotFields n j (.scalar sc') ++
        [.aggregate 0 (encodeRawAbstractByteVals mergedBytes)]) := by
    unfold finalizeUnionFieldsWithRawOverlayOpt
    rw [hre_enc]
    dsimp only
    rw [hneq_bytes]
    dsimp only
    rw [forceValueListOpt_eq_some]
    dsimp only
    rw [appendValueList_eq_append, forceValueListOpt_eq_some]
  unfold writeProjectedForLocal
  rw [htouch, hdecl_u]
  dsimp only
  unfold writeProjectedValueUnionAware
  dsimp only
  rw [hr_base, hk_u, hlookup]
  dsimp only
  rw [hfu]
  dsimp only
  rw [hble_j]; simp only []
  rw [hbase_enc, hcons]
  simp only [Bool.true_or, unionActiveSlotIsZstPlaceholder]
  rw [encodeTypedValueToBytes_primScalar hprim himm' (by
    cases isUnresolvedLayoutIdx body.layouts fty.layoutIdx
    · rfl
    · cases get? tl.fieldLayouts j
      · exact resolveTyWithLocalDecls_kind_eq body.localDecls body.layouts fty
      · rfl)]
  dsimp only
  simp only [unionSlotLacksLayoutFreeImage]
  rw [hwrite_at, hrebuild]
  dsimp only
  rw [hfin]

private theorem listByteEq_refl : ∀ xs : List UInt8, listByteEq xs xs = true
  | [] => rfl
  | x :: xs => by simp [listByteEq, listByteEq_refl xs]

private theorem stringEq_self (s : String) : stringEq s s = true :=
  listByteEq_refl s.toByteArray.data.toList

private theorem collectAdtLayoutsInTyAux_mono :
    ∀ (fuel : Nat) (layouts : LayoutTable) (d : DefPath) (ty : Ty) (acc : List TypeLayout)
      {x : TypeLayout},
      x ∈ acc → x ∈ collectAdtLayoutsInTyAux fuel layouts d ty acc
  | 0, _, _, _, _, _, hx => hx
  | fuel + 1, layouts, d, ty, acc, x, hx => by
    unfold collectAdtLayoutsInTyAux
    dsimp only
    cases hk : ty.kind with
    | adt dp _ =>
      dsimp only
      cases hs : stringEq dp d
      · dsimp only; exact hx
      · dsimp only
        cases hl : layouts.lookup ty.layoutIdx
        · dsimp only; exact hx
        · dsimp only; exact List.mem_cons_of_mem _ hx
    | tuple elemKinds =>
      dsimp only
      let flIdxs := match layouts.lookup ty.layoutIdx with | some l => l.fieldLayouts | none => []
      suffices ∀ (ks : List RigidTy) (fls : List Nat) (a : List TypeLayout),
          x ∈ a →
          x ∈ collectAdtLayoutsInTupleAux
            (fun ek flIdx a' => collectAdtLayoutsInTyAux fuel layouts d ⟨ek, flIdx⟩ a') ks fls a from
        this elemKinds flIdxs acc hx
      intro ks
      induction ks with
      | nil => intro _ _ ha; dsimp only [collectAdtLayoutsInTupleAux]; exact ha
      | cons k rest ih =>
        intro fls a ha
        cases fls with
        | nil =>
          dsimp only [collectAdtLayoutsInTupleAux]
          exact ih [] _ (collectAdtLayoutsInTyAux_mono fuel layouts d ⟨k, 0⟩ a ha)
        | cons fl flRest =>
          dsimp only [collectAdtLayoutsInTupleAux]
          exact ih flRest _ (collectAdtLayoutsInTyAux_mono fuel layouts d ⟨k, fl⟩ a ha)
    | array ek _ =>
      dsimp only
      cases hl : layouts.lookup ty.layoutIdx with
      | none => exact hx
      | some l =>
        cases l with | mk _ _ _ lf _ _ lfls =>
        cases lf <;> try exact hx
        cases lfls with
        | nil => exact hx
        | cons fl _ =>
          dsimp only
          exact collectAdtLayoutsInTyAux_mono fuel layouts d ⟨ek, fl⟩ acc hx
    | slice ek =>
      dsimp only
      cases hl : layouts.lookup ty.layoutIdx with
      | none => exact hx
      | some l =>
        cases l with | mk _ _ _ lf _ _ lfls =>
        cases lf <;> try exact hx
        cases lfls with
        | nil => exact hx
        | cons fl _ =>
          dsimp only
          exact collectAdtLayoutsInTyAux_mono fuel layouts d ⟨ek, fl⟩ acc hx
    | _ => dsimp only; exact hx

private theorem mem_collectAdtLayoutsInDecls {layouts : LayoutTable} {d : DefPath}
    {args : List RigidTy} {tl : TypeLayout} :
    ∀ (decls : List LocalDecl) {u : Nat} {uDecl : LocalDecl},
      get? decls u = some uDecl →
      uDecl.ty.kind = .adt d args →
      layouts.lookup uDecl.ty.layoutIdx = some tl →
      tl ∈ collectAdtLayoutsInDecls layouts d decls
  | [], _, _, h, _, _ => nomatch h
  | decl :: rest, 0, uDecl, h, hk, hl => by
    injection h with h; subst h
    cases decl with | mk dm dty =>
    cases dty with | mk dk dl =>
    dsimp only at hk hl ⊢
    subst hk
    dsimp only [collectAdtLayoutsInDecls, collectAdtLayoutsInTyAux]
    rw [stringEq_self]
    dsimp only
    rw [hl]
    exact List.mem_cons_self
  | decl :: rest, u + 1, uDecl, h, hk, hl => by
    unfold collectAdtLayoutsInDecls
    exact collectAdtLayoutsInTyAux_mono 6 layouts d decl.ty _
      (mem_collectAdtLayoutsInDecls rest h hk hl)

private theorem findExactFieldLayoutUnionInList_mem {localDecls : List LocalDecl}
    {layouts : LayoutTable} {fIdx targetFlIdx : Nat} {valOpt : Option Value}
    {opTyOpt : Option Ty} {info : Nat × TypeLayout} :
    ∀ (ls : List TypeLayout),
      findExactFieldLayoutUnionInList localDecls layouts fIdx targetFlIdx valOpt opTyOpt ls =
        some info →
      ∃ l ∈ ls, unionLayoutAcceptsActiveField localDecls layouts l fIdx valOpt opTyOpt = some info
  | [], h => nomatch h
  | l :: rest, h => by
    unfold findExactFieldLayoutUnionInList at h
    dsimp only at h
    cases hg : get? l.fieldLayouts fIdx with
    | none =>
      rw [hg] at h; dsimp only at h
      obtain ⟨l', hl', ha⟩ := findExactFieldLayoutUnionInList_mem rest h
      exact ⟨l', List.mem_cons_of_mem _ hl', ha⟩
    | some flIdx =>
      rw [hg] at h; dsimp only at h
      cases hb : Nat.beq flIdx targetFlIdx
      · rw [hb] at h; dsimp only at h
        obtain ⟨l', hl', ha⟩ := findExactFieldLayoutUnionInList_mem rest h
        exact ⟨l', List.mem_cons_of_mem _ hl', ha⟩
      · rw [hb] at h; dsimp only at h
        cases ha : unionLayoutAcceptsActiveField localDecls layouts l fIdx valOpt opTyOpt with
        | some info' =>
          rw [ha] at h; injection h with h; subst h
          exact ⟨l, List.mem_cons_self, ha⟩
        | none =>
          rw [ha] at h; dsimp only at h
          obtain ⟨l', hl', ha'⟩ := findExactFieldLayoutUnionInList_mem rest h
          exact ⟨l', List.mem_cons_of_mem _ hl', ha'⟩

private theorem findExactSizeUnionInList_mem {localDecls : List LocalDecl}
    {layouts : LayoutTable} {fIdx targetSz : Nat} {valOpt : Option Value}
    {opTyOpt : Option Ty} {info : Nat × TypeLayout} :
    ∀ (ls : List TypeLayout),
      findExactSizeUnionInList localDecls layouts fIdx targetSz valOpt opTyOpt ls = some info →
      ∃ l ∈ ls, unionLayoutAcceptsActiveField localDecls layouts l fIdx valOpt opTyOpt = some info
  | [], h => nomatch h
  | l :: rest, h => by
    unfold findExactSizeUnionInList at h
    cases hc : Nat.beq l.size.bytes targetSz
    · rw [hc] at h; dsimp only at h
      obtain ⟨l', hl', ha⟩ := findExactSizeUnionInList_mem rest h
      exact ⟨l', List.mem_cons_of_mem _ hl', ha⟩
    · rw [hc] at h; dsimp only at h
      cases ha : unionLayoutAcceptsActiveField localDecls layouts l fIdx valOpt opTyOpt with
      | some info' =>
        rw [ha] at h; injection h with h; subst h
        exact ⟨l, List.mem_cons_self, ha⟩
      | none =>
        rw [ha] at h; dsimp only at h
        obtain ⟨l', hl', ha'⟩ := findExactSizeUnionInList_mem rest h
        exact ⟨l', List.mem_cons_of_mem _ hl', ha'⟩

/-- Evaluating `Rvalue.aggregate (.adt d 0 (some f)) [op]` (`f < n`) for a
well-typed union `uDecl` produces `.ok (.aggregate 0 (unionSlotFields n f (.scalar sc)))`
whenever `op` evaluates to `.scalar sc`, and `.ub` whenever `op` fails with `.ub`. -/
theorem evalRvalue_unionAggregate_activeField_eq
    {body : CapturedMir} {locals : List LocalSlot} {mem : Memory}
    (hbor : mem.borrows = .nil) (hcaller : mem.callerLocals = .nil)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {u : Local} {uDecl : LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {d : DefPath} (hadt : ∃ args, uDecl.ty.kind = .adt d args)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl)
    {fTy : Ty} (hprim : IsPrimScalarTy fTy)
    (hfl_sz : fl.layout.size = (translateTy fTy body.layouts).layout.size)
    {op : MirAst.Operand} (hop : WellTypedScalarOperand body tf op fTy)
    (hdecls_adt : ∀ l ∈ collectAdtLayoutsInDecls body.layouts d body.localDecls,
      body.layouts.lookup uDecl.ty.layoutIdx = some l) :
    (evalOperand locals op .nil mem.globals body.layouts .nil = .ub →
      evalRvalue locals (.aggregate (.adt d 0 (some f)) [op]) mem body.localDecls body.layouts =
        .ub) ∧
    (∀ (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt),
      evalOperand locals op .nil mem.globals body.layouts .nil = .ok (.scalar sc) locals →
      ImmediateRel fTy body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)) →
      evalRvalue locals (.aggregate (.adt d 0 (some f)) [op]) mem body.localDecls body.layouts =
        .ok (.aggregate 0 (unionSlotFields n f (.scalar sc))) locals mem) := by
  have hop_ld := hop.evalOperand_localDecls_eq locals mem.globals
  refine ⟨fun hub => ?_, fun sc msc hok himm => ?_⟩
  · unfold evalRvalue
    dsimp only
    unfold evalAggregateAdt evalOperands
    rw [hbor, hcaller, hop_ld, hub]
  · obtain ⟨args_u, hk_d⟩ := hadt
    obtain ⟨tl', flIdx, fTl, hlookup', hgf, hlf, rfl⟩ := unionFieldLayoutOf_lookup_eq hwt hfl
    obtain ⟨_, _, tl, n', hk_u, _, _, hlookup, hfu, hvar, huninh, _, hfl_len, _, _, hadt_fields⟩ :=
      hwt.adt_spec
    rw [hlookup] at hlookup'; injection hlookup' with htl_eq; subst htl_eq
    have hn_eq : n' = n := by
      unfold translateTy at hfields
      dsimp only at hfields
      rw [hk_u, hlookup] at hfields
      dsimp only [translateTypeLayout, translateFieldsShape] at hfields
      rw [hfu] at hfields; cases hfields; rfl
    simp only [hn_eq] at *
    obtain ⟨fTl', hlf', hfTl_uninh, hvb_f, _, henc_slot⟩ := hadt_fields f flIdx hgf
    rw [hlf] at hlf'; injection hlf' with hfTl_eq; subst hfTl_eq
    cases himm with
    | scalar _ _ hrel_sc hsz_fTy hbool hchar =>
    have himm : ImmediateRel fTy body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)) :=
      .scalar sc msc hrel_sc hsz_fTy hbool hchar
    have hvb_sc : ValidScalarBytes sc.sizeBytes := hrel_sc.validBytes
    have hsc_sz : sc.sizeBytes = fTl.size.bytes :=
      translateSizeBytes_inj hvb_sc hvb_f (hsz_fTy.symm.trans hfl_sz.symm)
    have henc8 := henc_slot fTy sc msc hprim himm hsc_sz 15
    have h0 : Nat.beq sc.sizeBytes 0 = false := by
      rcases hvb_sc with h | h | h | h | h <;> (rw [h]; rfl)
    have henc_sc : encodeScalarBytes sc none =
        some (encodeLittleEndianBytes sc.bits sc.sizeBytes none) := by
      simp [encodeScalarBytes, h0]
    have hopTy_eq := hop.operandTy_eq
    have hopTy_kind : ∃ oTy, operandTy body.localDecls body.layouts op = some oTy ∧
        oTy.kind = fTy.kind := ⟨fTy, hopTy_eq, rfl⟩
    obtain ⟨oTy, hoTy_eq, hoTy_kind⟩ := hopTy_kind
    have hval_ty : validateValueForTy? body.layouts (some oTy) (.scalar sc) = true := by
      cases sc with | mk bits szB =>
      exact validateValueForTy?_primScalar body.layouts hprim hvb_sc hsz_fTy
        (fun r hr => Option.some.inj hr ▸ hoTy_kind)
        (fun hb => (hbool hb).2) (fun hc => (hchar hc).2)
    let rOpTy := resolveTyWithLocalDecls body.localDecls body.layouts oTy
    have hrOp_kind : rOpTy.kind = fTy.kind :=
      (resolveTyWithLocalDecls_kind_eq body.localDecls body.layouts oTy).trans hoTy_kind
    have hval_rOp : validateValueForTy? body.layouts (some rOpTy) (.scalar sc) = true := by
      cases sc with | mk bits szB =>
      exact validateValueForTy?_primScalar body.layouts hprim hvb_sc hsz_fTy
        (fun r hr => Option.some.inj hr ▸ hrOp_kind)
        (fun hb => (hbool hb).2) (fun hc => (hchar hc).2)
    have henc_rOp := encodeTypedValueToBytes_primScalar hprim himm hrOp_kind
    have htySz_rOp := tyByteSize_primScalar (localDecls := body.localDecls) hprim hvb_sc hsz_fTy
      hrOp_kind
    have hblt_f : Nat.blt f n = true := Nat.ble_eq.mpr hf
    have haccept : unionLayoutAcceptsActiveField body.localDecls body.layouts tl f
        (some (.scalar sc)) (some oTy) = some (n, tl) := by
      unfold unionLayoutAcceptsActiveField layoutIsSingleVariantUnion
      simp only [huninh, hvar, hfu]
      rw [hblt_f]
      dsimp only
      change (match (match validateValueForTy? body.layouts (some rOpTy) (.scalar sc) with
          | false => false
          | true =>
            match encodeTypedValueToBytes body.layouts rOpTy (.scalar sc) with
            | some _ => true | none => false) with
        | false => none
        | true => _) = _
      rw [hval_rOp, henc_rOp]
      dsimp only
      rw [hgf]; dsimp only; rw [hlf]
      dsimp only
      rw [hfTl_uninh]
      dsimp only
      change (match (match tyByteSize body.localDecls body.layouts rOpTy with
          | some opSz => Nat.beq opSz fTl.size.bytes
          | none => true) with
        | false => none
        | true => _) = _
      rw [htySz_rOp, ← hsc_sz]; dsimp only; rw [Nat.beq_refl]
      dsimp only [defaultCodecFuel]
      rw [henc8, henc_sc]
    have hmem_tl := mem_collectAdtLayoutsInDecls body.localDecls hdecl_u hk_d hlookup
    have hall_eq : ∀ l ∈ collectAdtLayoutsInDecls body.layouts d body.localDecls, l = tl := by
      intro l hl
      have hlk := hdecls_adt l hl
      rw [hlookup] at hlk
      exact (Option.some.inj hlk).symm
    obtain ⟨l₀, lRest, hdecls_cons⟩ :
        ∃ l₀ lRest, collectAdtLayoutsInDecls body.layouts d body.localDecls = l₀ :: lRest := by
      cases h : collectAdtLayoutsInDecls body.layouts d body.localDecls with
      | nil => rw [h] at hmem_tl; cases hmem_tl
      | cons l₀ lRest => exact ⟨l₀, lRest, rfl⟩
    have hall_unions : allLayoutsAreUnions (l₀ :: lRest) = true := by
      suffices ∀ ls, (∀ l ∈ ls, l = tl) → allLayoutsAreUnions ls = true from
        this (l₀ :: lRest) (hdecls_cons ▸ hall_eq)
      intro ls
      induction ls with
      | nil => intro _; rfl
      | cons x xs ih =>
        intro hxs
        have hx := hxs x List.mem_cons_self
        subst hx
        simp [allLayoutsAreUnions, layoutIsSingleVariantUnion, hvar, hfu,
          ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy))]
    have hfind_any : findMatchingUnionCountInList.findAny body.localDecls body.layouts f
        (some (.scalar sc)) (some oTy) (l₀ :: lRest) = some (n, tl) := by
      have hl₀ : l₀ = tl := hall_eq l₀ (hdecls_cons ▸ List.mem_cons_self)
      subst hl₀
      unfold findMatchingUnionCountInList.findAny
      rw [haccept]
    have h_after_fl :
        (match
          match tyByteSize body.localDecls body.layouts
              (resolveTyWithLocalDecls body.localDecls body.layouts oTy) with
          | some opSz =>
            findExactSizeUnionInList body.localDecls body.layouts f opSz
              (some (.scalar sc)) (some oTy) (l₀ :: lRest)
          | none => none with
        | some info => some info
        | none =>
          findMatchingUnionCountInList.findAny body.localDecls body.layouts f
            (some (.scalar sc)) (some oTy) (l₀ :: lRest)) = some (n, tl) := by
      cases hs : tyByteSize body.localDecls body.layouts
          (resolveTyWithLocalDecls body.localDecls body.layouts oTy) <;> dsimp only
      · exact hfind_any
      · cases hexSz : findExactSizeUnionInList body.localDecls body.layouts f _
            (some (.scalar sc)) (some oTy) (l₀ :: lRest) <;> dsimp only
        · exact hfind_any
        · obtain ⟨l', hl', ha'⟩ := findExactSizeUnionInList_mem _ hexSz
          rw [hall_eq l' (hdecls_cons ▸ hl'), haccept] at ha'
          exact ha'.symm
    have hfind_match : findMatchingUnionCountInList body.localDecls body.layouts f
        (some (.scalar sc)) (some oTy) (l₀ :: lRest) = some (n, tl) := by
      unfold findMatchingUnionCountInList
      dsimp only
      cases hi : isUnresolvedLayoutIdx body.layouts
          (resolveTyWithLocalDecls body.localDecls body.layouts oTy).layoutIdx <;> dsimp only
      · cases hexFl : findExactFieldLayoutUnionInList body.localDecls body.layouts f
            (resolveTyWithLocalDecls body.localDecls body.layouts oTy).layoutIdx
            (some (.scalar sc)) (some oTy) (l₀ :: lRest) <;> dsimp only
        · exact h_after_fl
        · obtain ⟨l', hl', ha'⟩ := findExactFieldLayoutUnionInList_mem _ hexFl
          rw [hall_eq l' (hdecls_cons ▸ hl'), haccept] at ha'
          exact ha'.symm
      · exact h_after_fl
    have hinfo : findAdtUnionInfo body.localDecls body.layouts d f
        (some (.scalar sc)) (some oTy) = some (some (n, tl)) := by
      unfold findAdtUnionInfo
      rw [hdecls_cons]; dsimp only
      rw [hall_unions]; dsimp only
      rw [hfind_match]
    have hfls_ne : ∃ a as, tl.fieldLayouts = a :: as := by
      cases h : tl.fieldLayouts with
      | nil =>
        have h0' : 0 = n := by rw [← hfl_len, h]; rfl
        rw [← h0'] at hf; cases hf
      | cons a as => exact ⟨a, as, rfl⟩
    obtain ⟨a, as, hfls_eq⟩ := hfls_ne
    unfold evalRvalue
    dsimp only
    unfold evalAggregateAdt evalOperands
    rw [hbor, hcaller, hop_ld, hok]
    dsimp only [evalOperands]
    unfold evalAggregateAdtUnionValue?
    simp only [hoTy_eq, hval_ty, hinfo, unionActiveSlotIsZstPlaceholder,
      unionSlotLacksLayoutFreeImage, attachUnionActiveFieldOverlayOpt, hfls_eq,
      forceValueListOpt_eq_some]
    rfl

/-! ## 5. Moving an Uninitialized Union Local to Memory -/

private theorem uAlign_roundtrip {align : Miri.ABI.Align} (h : align.pow2 ≤ 29) :
    Miri.ABI.Align.bytes align = .ok (UInt64.shiftLeft 1 (UInt64.ofNat align.pow2)) ∧
    Miri.ABI.Align.fromBytes (UInt64.shiftLeft 1 (UInt64.ofNat align.pow2)) = .ok align := by
  have H : ∀ p ≤ 29,
      Miri.ABI.Align.fromBytes (UInt64.shiftLeft 1 (UInt64.ofNat p)) = .ok ⟨p⟩ := by
    decide
  rcases align with ⟨p⟩
  refine ⟨?_, H p h⟩
  have hp' : p ≤ 29 := h
  have hp : ¬ p ≥ 64 := by omega
  simp only [Miri.ABI.Align.bytes, hp, ↓reduceIte]

/-- `Allocation.tryNew` of a fresh uninitialized stack allocation (as
`annealPlaceHooks.allocateStack` calls it) succeeds for every alignment that a
translated layout can have, and yields a mutable allocation of the requested
size and alignment, without provenance or native buffer, all of whose bytes are
uninitialized. -/
theorem freshUnionAlloc_spec (size : Miri.ABI.Size) (align : Miri.ABI.Align)
    (h : align.pow2 ≤ 29) :
    ∃ alloc : Miri.Memory.Allocation AnnealProv Unit,
      Miri.Memory.Allocation.tryNew size align .Uninit annealZeroedStorage = .ok alloc ∧
      alloc.byteSize = size ∧ alloc.len = size.bytes.toNat ∧ alloc.nativeBuffer = none ∧
      alloc.mutability = .Mut ∧ alloc.align = align ∧
      alloc.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      alloc.initializationMask = Miri.Memory.InitMask.new size false := by
  obtain ⟨hb, hn⟩ := uAlign_roundtrip h
  obtain ⟨a, htry, hsz, hlen, hnat, hmut, hal⟩ :=
    Miri.Memory.Allocation.tryNew_replicate_full (P := AnnealProv) size align _ hb hn
  obtain ⟨hprov, hmask⟩ := Miri.Memory.Allocation.tryNew_uninit_shape size align a htry
  exact ⟨a, htry, hsz, hlen, hnat, hmut, hal, hprov, hmask⟩

/-- `annealPlaceHooks.allocateStack` reserves the fresh `AllocId` and records
the allocation that `tryNew` built. -/
theorem annealPlaceHooks_allocateStack_eq {ld : List LocalDecl} {ly : LayoutTable}
    {m : AnnealStepState} {layout : Miri.Interpreter.LocalLayout}
    {alloc : Miri.Memory.Allocation AnnealProv Unit}
    (htry : Miri.Memory.Allocation.tryNew layout.layout.size layout.layout.align.abi .Uninit
      annealZeroedStorage = .ok alloc)
    {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id)) :
    (annealPlaceHooks ld ly).allocateStack () layout m =
      .ok ⟨stackAllocPlace id, layout⟩
        { m with machine := stackAllocMachine m.machine mem' id (alloc.withExtra none) } := by
  simp only [annealPlaceHooks, htry, hres, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, set, MonadStateOf.set, EStateM.set, pure, EStateM.pure]
  rfl

/-- `forceAllocation` of an uninitialized immediate local: it caches the
local's layout, moves the local into a fresh stack allocation, writes nothing
(the allocation stays uninitialized), and returns the allocation's place. -/
theorem forceAllocation_uninit_eq
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Nat} {decl : LocalDecl} (hlt : idx < tf.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hcache : ∀ l, (tf.locals[idx]'hlt).layout = some l → l = translateTy decl.ty body.layouts)
    (hval : (tf.locals[idx]'hlt).value = .live (.immediate .uninit))
    (hsized : (translateTy decl.ty body.layouts).layout.isSized = true)
    {alloc : Miri.Memory.Allocation AnnealProv Unit}
    (htry : Miri.Memory.Allocation.tryNew (translateTy decl.ty body.layouts).layout.size
      (translateTy decl.ty body.layouts).layout.align.abi .Uninit annealZeroedStorage = .ok alloc)
    {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id))
    (ident : Miri.Interpreter.LocalsIdentity) (lay : Miri.Interpreter.LocalLayout)
    (hlt' : idx < (cacheFrameLocalLayout tf idx hlt (translateTy decl.ty body.layouts)).locals.size) :
    Miri.Interpreter.forceAllocation (annealPlaceHooks body.localDecls body.layouts) ()
        ⟨.local 0 idx none ident, lay⟩ m =
      .ok ⟨stackAllocPlace id, lay⟩
        { stack := ⟨#[setFrameLocalIndirect
            (cacheFrameLocalLayout tf idx hlt (translateTy decl.ty body.layouts)) idx hlt'
            (stackAllocPlace id)]⟩,
          machine := stackAllocMachine m.machine mem' id (alloc.withExtra none) } := by
  have hgo : tf.getLocalOperand idx = .ok (.immediate .uninit) := by
    unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
      Miri.Interpreter.LocalState.access
    simp [hlt, hval, bind, Except.bind, pure, Except.pure, Except.mapError]
  have hval' : ((cacheFrameLocalLayout tf idx hlt
      (translateTy decl.ty body.layouts)).locals[idx]'hlt').value = .live (.immediate .uninit) := by
    simp [cacheFrameLocalLayout, hval]
  have halloc := annealPlaceHooks_allocateStack_eq (ld := body.localDecls) (ly := body.layouts)
    (m := { m with stack := ⟨#[cacheFrameLocalLayout tf idx hlt
      (translateTy decl.ty body.layouts)]⟩ }) htry hres
  unfold Miri.Interpreter.forceAllocation
  simp only [Miri.Interpreter.requireCurrent_eq,
    Miri.Interpreter.checkLocalIdentity_debugOff (annealPlaceHooks _ _) _ rfl,
    bind, EStateM.bind, annealPlaceHooks_frameIndex_eq hframes]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure,
    annealPlaceHooks_getFrame_eq hframes]
  rw [hgo, Miri.Interpreter.stackLift_ok]
  simp only [pure, EStateM.pure]
  rw [EStateM.bind_apply_ok (placeLayoutOfLocal_eq hframes hlt hdecl hcache)]
  simp only [hsized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [EStateM.bind_apply_ok halloc]
  simp only [EStateM.bind, pure, EStateM.pure, annealPlaceHooks_afterLocalMovedToMemory_eq,
    annealPlaceHooks_getFrame_mk, frame_setLocalOperand_live hlt' hval',
    Miri.Interpreter.stackLift_ok, annealPlaceHooks_setFrame_mk]
  rfl

/-- Projecting a memory-backed union to field `j < n` with the aggregate
context: offset `0`, and the field layout from the union's `TypeLayout`. -/
theorem projectField_unionAggregate
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (layouts : LayoutTable) (mach : AnnealMachine)
    {uLay : Miri.Interpreter.LocalLayout} {n j : Nat}
    (hfields : uLay.layout.fields = .Union n) (hj : j < n)
    {fl : Miri.Interpreter.LocalLayout} (hfl : unionFieldLayoutOf layouts uLay j = some fl)
    (hsized : fl.layout.isSized = true)
    {mp : Miri.Interpreter.MemPlace AnnealProv} (hmeta : mp.metadata = .none) :
    Miri.Interpreter.projectField (annealUnionAggregateCx frame layouts mach)
        ⟨.indirect mp, uLay⟩ j =
      .ok ⟨.indirect mp, fl⟩ := by
  have hoff : uLay.layout.fields.offset j = .ok Miri.ABI.Size.ZERO := by
    rw [hfields]
    unfold Miri.ABI.FieldsShape.offset Miri.ABI.FieldsShape.count
    have : ¬ j ≥ n := by omega
    simp [this, pure, Except.pure]
  unfold Miri.Interpreter.projectField
  simp only [bind, Except.bind, hoff, Except.mapError]
  simp only [annealUnionAggregateCx, hfields, hfl, hsized, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, pure, Except.pure]
  unfold Miri.Interpreter.OpTy.offsetWithMeta
  simp only [annealProjectionCx, bind, Except.bind, projectionMemoryOffset_zero,
    memPlace_offset_zero_eq mp hmeta, pure, Except.pure]

/-! ## 6. Union Aggregates -/

/-- `writeAggregate` of a union aggregate with active field `f` and its one
operand: downcast to variant `0`, project to field `f`, evaluate the operand,
copy it into the field, and write the (trivial) discriminant. -/
theorem writeAggregate_union_def {P S C V : Type}
    (h : Miri.Interpreter.AggregateHooks P S C V) (choice : C)
    (d : Miri.MIR.DefId) (args : Array Miri.MIR.GenericArg)
    (ut : Option Miri.MIR.UserTypeAnnotationIndex) (f : Nat) (op : Miri.MIR.Operand)
    (dest : V) :
    Miri.Interpreter.writeAggregate h choice (.Adt d 0 args ut (some f)) #[op] dest =
      (do
        let variantDest ← h.projectDowncast choice dest 0
        let field ← h.projectField choice variantDest f
        let operand ← h.evalOperandAt choice (Miri.Interpreter.OperandPath.aggregate 0) op
          (some (h.placeLayout field))
        h.copyOpNoValidate choice operand field false
        h.writeDiscriminant choice 0 dest
        if ← h.enforceValidity choice (h.placeLayout dest) then
          h.validate choice dest) := by
  unfold Miri.Interpreter.writeAggregate
  simp [Std.Legacy.Range.forIn_eq_forIn_range']

/-- A scalar constant or `copy` of an unprojected local is evaluated by
`annealEvalOperand` under the `LM-2.4` hooks too. -/
theorem annealEvalOperandLM2_4_scalar {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty} (hop : WellTypedScalarOperand body tf op ty)
    (known : Option Miri.Interpreter.LocalLayout) :
    annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) known =
      annealEvalOperand body.localDecls body.layouts (translateOperand op) known := by
  cases hop <;> rfl

/-- Evaluating a scalar constant or `copy` of an immediate local as a union
aggregate's operand, on a frame where the union destination `dstIdx` has
already moved to memory (`setFrameLocalIndirect`), under any machine `mach'`:
both machines report undefined behavior, or both produce related scalars, and
`lean-miri` only caches the copied local's layout. -/
theorem evalScalarOperand_union_dst
    {body : CapturedMir} {mach mach' : AnnealMachine} {af : StackFrame}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Local} {op : MirAst.Operand} {ty : Ty}
    (hframe : FrameRelLM2_4 body mach af tf)
    (hprim : IsPrimScalarTy ty)
    (hop : WellTypedScalarOperand body tf op ty)
    (hne : ∀ idx, op = .copy ⟨idx, .nil⟩ → idx ≠ dstIdx)
    (hlt_dst : dstIdx < tf.locals.size)
    (mp : Miri.Interpreter.MemPlace AnnealProv)
    (globals : List CapturedAllocation)
    (path : Miri.Interpreter.OperandPath)
    (known : Option Miri.Interpreter.LocalLayout) :
    let st : AnnealStepState :=
      { stack := ⟨#[setFrameLocalIndirect tf dstIdx hlt_dst mp]⟩, machine := mach' }
    (evalOperand af.locals op .nil globals body.layouts .nil = .ub ∧
      ∃ m' msg,
        (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt () path
          (translateOperand op) known st = .error (.undefinedBehavior msg) m') ∨
    (∃ sc msc tf', ∃ hlt_dst' : dstIdx < tf'.locals.size,
      evalOperand af.locals op .nil globals body.layouts .nil = .ok (.scalar sc) af.locals ∧
      (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt () path
        (translateOperand op) known st =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy ty body.layouts⟩
          { stack := ⟨#[setFrameLocalIndirect tf' dstIdx hlt_dst' mp]⟩, machine := mach' } ∧
      FrameRelLM2_4 body mach af tf' ∧
      (MemoryAllocDisjoint tf → MemoryAllocDisjoint tf') ∧
      (∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
      tf' = { tf with locals := tf'.locals } ∧
      (∀ j, j ≠ dstIdx → ∀ mls, tf.locals[j]? = some mls →
        ∃ mls', tf'.locals[j]? = some mls' ∧ mls'.value = mls.value) ∧
      ScalarRel sc msc ∧
      ImmediateRel ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc))) := by
  dsimp only
  let tf_ind := setFrameLocalIndirect tf dstIdx hlt_dst mp
  let st : AnnealStepState := { stack := ⟨#[tf_ind]⟩, machine := mach' }
  have hlm : ∀ (st' : AnnealStepState),
      (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt () path
        (translateOperand op) known st' =
      (do
        let opTy ← annealEvalOperand body.localDecls body.layouts (translateOperand op) known
        let imm ← annealReadImmediateLM2_2 opTy
        return (⟨.immediate imm.imm, imm.layout⟩ : Miri.Interpreter.OpTy AnnealProv)) st' := by
    intro st'
    simp only [annealAggregateHooksLM2_4, annealEvalOperandLM2_4_scalar hop known]
  rw [hlm]
  cases hop with
  | constScalar c sc hval hprim_c hsz hcan hlaysz hbool hchar =>
    obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
    have heval_a : evalOperand af.locals (.constant c) .nil globals body.layouts .nil =
        .ok (.scalar sc) af.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    have heval_m : annealEvalOperand body.localDecls body.layouts
        (translateOperand (.constant c)) known st =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ st := by
      with_unfolding_all
        unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
        dsimp only
        rw [hval]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton st.stack tf_ind rfl, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry, hprim_c.layoutOfEncoded]
    refine Or.inr ⟨sc, msc, tf, hlt_dst, heval_a, ?_, hframe, id, (fun _ h => h), rfl,
      (fun j _ mls hmls => ⟨mls, hmls, rfl⟩), hrel,
      .scalar sc msc hrel hlaysz hbool hchar⟩
    rw [EStateM.bind_eq_ok heval_m]
    rfl
  | copyLocal idx decl hdecl hsz_nz himm =>
    have hne' : idx ≠ dstIdx := hne idx rfl
    obtain ⟨slot, mls, _, hlt_idx, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
    have hlt_ind : idx < tf_ind.locals.size := by
      unfold tf_ind setFrameLocalIndirect; simp [hlt_idx]
    have hmls_ind : tf_ind.locals[idx]'hlt_ind = mls :=
      Option.some.inj (by
        rw [← Array.getElem?_eq_getElem]
        dsimp only [tf_ind, setFrameLocalIndirect]
        rw [Array.getElem?_set_ne _ hne'.symm]
        exact hmls)
    have himm' := himm mls hmls
    have hloc_base : LocalRel mach decl body.layouts slot mls := by
      cases hloc with
      | base _ _ hl => exact hl
      | union _ _ _ _ _ mp' _ _ _ _ _ _ => exact absurd rfl (himm' mp')
    cases hloc_base with
    | dead cachedLayout hcache =>
      left
      have hdead := annealEvalOperand_copy_dead (m := st) (topFrame := tf_ind) (known := known)
        rfl hlt_ind hdecl hmls_ind hcache
      dsimp only [st] at hdead
      refine ⟨by simp [evalOperand, hslot],
        { stack := ⟨#[cacheFrameLocalLayout tf_ind idx hlt_ind (translateTy decl.ty body.layouts)]⟩,
          machine := mach' },
        "read of dead local", ?_⟩
      dsimp only [translateOperand, translatePlace, List.map, List.toArray]
      exact EStateM.bind_eq_error hdead
    | indirect _ mp' _ _ _ _ =>
      exact False.elim (himm' mp' rfl)
    | immediate _ imm cachedLayout hcache hval =>
      let tf' := cacheFrameLocalLayout tf idx hlt_idx (translateTy decl.ty body.layouts)
      have hlt_dst' : dstIdx < tf'.locals.size := by
        unfold tf' cacheFrameLocalLayout; simp [hlt_dst]
      have hcomm : cacheFrameLocalLayout tf_ind idx hlt_ind (translateTy decl.ty body.layouts) =
          setFrameLocalIndirect tf' dstIdx hlt_dst' mp :=
        cacheFrameLocalLayout_setFrameLocalIndirect_comm tf hlt_dst hlt_idx hne' mp
          (translateTy decl.ty body.layouts)
      have hlive := annealEvalOperand_copy_live (m := st) (topFrame := tf_ind) (known := known)
        rfl hlt_ind hdecl hmls_ind hcache
      dsimp only [st] at hlive
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · left
        refine ⟨by simp [evalOperand, hslot],
          { stack := ⟨#[cacheFrameLocalLayout tf_ind idx hlt_ind (translateTy decl.ty body.layouts)]⟩,
            machine := mach' },
          "read of uninitialized local", ?_⟩
        dsimp only [translateOperand, translatePlace, List.map, List.toArray]
        rw [EStateM.bind_eq_ok hlive]
        rfl
      · right
        obtain ⟨sc, msc, rfl, rfl, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩ :=
          himmRel.of_primitive_scalar hprim
        have ha : evalOperand af.locals (.copy ⟨idx, .nil⟩) .nil globals body.layouts .nil =
            .ok (.scalar sc) af.locals := by
          simp [evalOperand, readProjectedValue, hslot]
        refine ⟨sc, msc, tf', hlt_dst', ha, ?_,
          hframe.cache_local_layout hdecl hlt_idx,
          ?_, (fun _ hj => hj.cache_layout hlt_idx _), rfl, ?_,
          hrel_sc, .scalar sc msc hrel_sc hsz_sc hbool_sc hchar_sc⟩
        · dsimp only [translateOperand, translatePlace, List.map, List.toArray]
          rw [EStateM.bind_eq_ok hlive]
          dsimp only [annealReadImmediateLM2_2, pure, EStateM.pure, bind, EStateM.bind]
          rw [hcomm]
        · intro hdisj
          apply MemoryAllocDisjoint.mono_layout hdisj
          intro k
          by_cases hk : k = idx
          · subst hk
            exists (translateTy decl.ty body.layouts)
            dsimp [tf', cacheFrameLocalLayout]
            rw [Array.getElem?_set]
            simp only [↓reduceIte]
            simp [hmls, hmls_eq]
          · exists (tf.locals[k]?).bind (fun x => x.layout)
            dsimp [tf', cacheFrameLocalLayout]
            rw [Array.getElem?_set_ne _ (Ne.symm hk)]
            cases tf.locals[k]? <;> rfl
        · intro j _ mls_j hmls_j
          by_cases hj : j = idx
          · subst hj
            have hget : tf.locals[j]'hlt_idx = mls_j := by
              have h := Array.getElem?_eq_getElem hlt_idx
              rw [hmls_j] at h
              exact (Option.some.inj h).symm
            refine ⟨{ tf.locals[j]'hlt_idx with
              layout := some (translateTy decl.ty body.layouts) }, ?_, by rw [hget]⟩
            dsimp [tf', cacheFrameLocalLayout]
            rw [Array.getElem?_set]
            simp only [↓reduceIte]
          · refine ⟨mls_j, ?_, rfl⟩
            dsimp [tf', cacheFrameLocalLayout]
            rw [Array.getElem?_set_ne _ (Ne.symm hj)]
            exact hmls_j

theorem setFrameLocalIndirect_congr
    {tf tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : tf = tf') {idx : Nat} (hlt : idx < tf.locals.size) (hlt' : idx < tf'.locals.size)
    (mp : Miri.Interpreter.MemPlace AnnealProv) :
    setFrameLocalIndirect tf idx hlt mp = setFrameLocalIndirect tf' idx hlt' mp := by
  subst h
  rfl

/-- Writing a related scalar at offset `0` of the fresh stack allocation `id`
(`stackAllocPlace id`) replaces that allocation by the result of
`union_writeScalar_prefix`. -/
theorem annealWriteImmediate_unionFresh
    {mach : AnnealMachine} {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    {A : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {destLay : Miri.Interpreter.LocalLayout}
    (hfresh : mem'.live.any (fun entry => entry.1 == id) = false)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    {S : Nat} (hlen : A.len = S) (hsz : A.byteSize = translateSizeBytes S) (hS : S ≤ 16)
    (hle : sc.sizeBytes ≤ S) (hmut : A.mutability = .Mut)
    (hprov : A.provenanceMap = Miri.Memory.ProvenanceMap.new)
    {M' : Miri.Memory.InitMask}
    (hset : A.initializationMask.setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) true =
        .ok M') :
    ∃ A' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc)) ⟨.memory (stackAllocPlace id), destLay⟩
          { stack := ⟨#[tf]⟩, machine := stackAllocMachine mach mem' id A } =
        .ok () { stack := ⟨#[tf]⟩, machine := stackAllocMachine mach mem' id A' } ∧
      A'.byteSize = A.byteSize ∧ A'.len = S ∧ A'.align = A.align ∧ A'.mutability = .Mut ∧
      A'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧ A'.initializationMask = M' ∧
      A'.extra = A.extra ∧ A'.nativeBuffer = A.nativeBuffer ∧
      (unionAllocRaw A').extract 0 sc.sizeBytes = allocLeBytes sc.bits sc.sizeBytes := by
  obtain ⟨A', hw, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    union_writeScalar_prefix hrel hlen hsz hS hle hmut hprov hset
  have hbase := lookupBaseAddr_stackAllocMachine_self mach mem' id A
  have hidx := findIdx?_push_fresh mem'.live id
    ({ kind := .stack, allocation := A } : Miri.Memory.LocalAllocation AnnealProv
      (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind) hfresh
  have hlive : (stackAllocMachine mach mem' id A).memory.live =
      mem'.live.push (id, ⟨.stack, A⟩) := rfl
  have hoff : Miri.ABI.Size.ofBytes
      ((Miri.ABI.Size.ofBytes (annealStackBaseAddr id)).bytes - annealStackBaseAddr id) =
      Miri.ABI.Size.ZERO := by
    simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
  have hmsc_sz : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).size = msc.size :=
    rfl
  refine ⟨A', ?_, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  unfold annealWriteImmediateLM2_2 annealWriteIndirectImmediate
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton ⟨#[tf]⟩ tf rfl, stackAllocPlace, Option.bind,
    Miri.Memory.Provenance.getAllocId, hbase, hlive, hidx, Array.getElem?_push_size,
    add_size_zero_bytes, hoff, hmsc_sz, hw, pure, EStateM.pure, set, MonadStateOf.set,
    EStateM.set, array_push_set!_size]
  rfl

/-- `annealUnionAggregateField` on an uninitialized immediate union local whose
layout is cached: the local moves into the fresh allocation `id`, and the
projection to field `f` (`f < n`) is that allocation's place, with the field
layout of the union's `TypeLayout`. -/
theorem annealUnionAggregateField_fresh
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {u : Nat} {uDecl : LocalDecl} (hlt : u < tf.locals.size)
    (hdecl : get? body.localDecls u = some uDecl)
    (hc : (tf.locals[u]'hlt).layout = some (translateTy uDecl.ty body.layouts))
    (hval : (tf.locals[u]'hlt).value = .live (.immediate .uninit))
    {n f : Nat} (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n) (hsized : (translateTy uDecl.ty body.layouts).layout.isSized = true)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl)
    (hfl_sized : fl.layout.isSized = true)
    {alloc : Miri.Memory.Allocation AnnealProv Unit}
    (htry : Miri.Memory.Allocation.tryNew (translateTy uDecl.ty body.layouts).layout.size
      (translateTy uDecl.ty body.layouts).layout.align.abi .Uninit annealZeroedStorage = .ok alloc)
    {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id))
    (ident : Miri.Interpreter.LocalsIdentity) :
    annealUnionAggregateField body.localDecls body.layouts
        ⟨.local 0 u none ident, translateTy uDecl.ty body.layouts⟩ f m =
      .ok ⟨.memory (stackAllocPlace id), fl⟩
        { stack := ⟨#[setFrameLocalIndirect tf u hlt (stackAllocPlace id)]⟩,
          machine := stackAllocMachine m.machine mem' id (alloc.withExtra none) } := by
  have hcf := cacheFrameLocalLayout_of_cached tf hlt hc
  have hlt' : u < (cacheFrameLocalLayout tf u hlt (translateTy uDecl.ty body.layouts)).locals.size :=
    by rw [hcf]; exact hlt
  have hforce := annealForceUnionAllocation_of_ok (forceAllocation_uninit_eq (body := body) hframes hlt
    hdecl (fun l hl => by rw [hc] at hl; exact (Option.some.inj hl).symm) hval hsized htry hres
    ident (translateTy uDecl.ty body.layouts) hlt')
  rw [setFrameLocalIndirect_congr hcf hlt' hlt] at hforce
  have hproj := projectField_unionAggregate (setFrameLocalIndirect tf u hlt (stackAllocPlace id))
    body.layouts (stackAllocMachine m.machine mem' id (alloc.withExtra none)) hfields hf hfl
    hfl_sized (mp := stackAllocPlace id) rfl
  unfold annealUnionAggregateField
  simp only [bind, EStateM.bind, hforce, get, getThe, MonadStateOf.get, EStateM.get,
    stack_currentFrame?_singleton _ (setFrameLocalIndirect tf u hlt (stackAllocPlace id)) rfl, hproj,
    pure, EStateM.pure]

/-- `annealStackBaseAddr id` leaves room for every union of at most `16`
bytes before the end of the address space. -/
theorem annealStackBaseAddr_add_lt (id : Miri.Memory.AllocId) {S : Nat} (hS : S ≤ 16) :
    (annealStackBaseAddr id).toNat + S < 2 ^ 64 := by
  have h2 : (annealStackBaseAddr id).toNat = (id.value.toNat * 2 ^ 32) % 2 ^ 64 := by
    unfold annealStackBaseAddr
    rw [UInt64.toNat_shiftLeft]
    simp [Nat.shiftLeft_eq]
  have hmm : (id.value.toNat * 2 ^ 32) % (2 ^ 32 * 2 ^ 32) =
      (id.value.toNat % 2 ^ 32) * 2 ^ 32 := Nat.mul_mod_mul_right _ _ _
  have hlt : id.value.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  rw [h2, show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, hmm]
  have : (id.value.toNat % 2 ^ 32) * 2 ^ 32 ≤ (2 ^ 32 - 1) * 2 ^ 32 :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- A primitive scalar local is never a union local. -/
theorem primScalar_ne_union_local {body : CapturedMir} {u idx : Local} {uDecl decl : LocalDecl}
    {S : Nat} (hdecl_u : get? body.localDecls u = some uDecl)
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hdecl : get? body.localDecls idx = some decl) (hprim : IsPrimScalarTy decl.ty) :
    idx ≠ u := by
  intro heq
  subst heq
  rw [hdecl_u] at hdecl
  cases hdecl
  obtain ⟨n, hn, _⟩ := hwt.fields_union
  rw [hprim.fields_primitive] at hn
  cases hn

section AggregateHookFields

variable (ld : List LocalDecl) (ly : LayoutTable)

theorem aggLM2_4_placeLayout (p : Miri.Interpreter.RuntimePlace AnnealProv) :
    (annealAggregateHooksLM2_4 ld ly).placeLayout p = p.layout := rfl

theorem aggLM2_4_projectDowncast (p : Miri.Interpreter.RuntimePlace AnnealProv) (v : Nat) :
    (annealAggregateHooksLM2_4 ld ly).projectDowncast () p v =
      if isUnionLayout p.layout then
        if v == 0 then pure p else throw (.invalidProgram "union downcast to a nonzero variant")
      else (annealAggregateHooksLM2_2 ld ly).projectDowncast () p v := rfl

theorem aggLM2_4_projectField (p : Miri.Interpreter.RuntimePlace AnnealProv) (i : Nat) :
    (annealAggregateHooksLM2_4 ld ly).projectField () p i =
      if isUnionLayout p.layout then annealUnionAggregateField ld ly p i
      else (annealAggregateHooksLM2_2 ld ly).projectField () p i := rfl

theorem aggLM2_4_copyOpNoValidate (src : Miri.Interpreter.OpTy AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (b : Bool) :
    (annealAggregateHooksLM2_4 ld ly).copyOpNoValidate () src dest b =
      (do let imm ← annealReadImmediateLM2_2 src; annealWriteImmediateLM2_2 imm.imm dest) := rfl

theorem aggLM2_4_writeDiscriminant (v : Nat) (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    (annealAggregateHooksLM2_4 ld ly).writeDiscriminant () v dest =
      (do let _ ← annealEnsureAllocated dest; pure ()) := rfl

theorem aggLM2_4_enforceValidity (l : Miri.Interpreter.LocalLayout) :
    (annealAggregateHooksLM2_4 ld ly).enforceValidity () l = pure true := rfl

theorem aggLM2_4_validate (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    (annealAggregateHooksLM2_4 ld ly).validate () dest = pure () := rfl

end AggregateHookFields

theorem UnionMemRel.of_live_base {mach mach' : AnnealMachine} {uTy : Ty} {layouts : LayoutTable}
    {S : Nat} {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a)
    (h : UnionMemRel mach uTy layouts S f0Ty sc mp) :
    UnionMemRel mach' uTy layouts S f0Ty sc mp := by
  cases h with
  | mk allocId tag baseAddr localAlloc msc hprov hmis hmeta hl hb hptr hovf hsz hlen hmut hp hal
      hex hnat hk hmask hrel hprim himm hraw =>
    exact .mk allocId tag baseAddr localAlloc msc hprov hmis hmeta (hlive _ hl)
      (by rw [hbase _ _ hl]; exact hb) hptr hovf hsz hlen hmut hp hal hex hnat hk hmask hrel hprim
      himm hraw

theorem UnionLocalRel.of_live_base {mach mach' : AnnealMachine} {decl : LocalDecl}
    {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a)
    (h : UnionLocalRel mach decl layouts slot mls) :
    UnionLocalRel mach' decl layouts slot mls := by
  cases h with
  | base _ _ hl => exact .base _ _ (hl.of_live_base hlive hbase)
  | union S n f f0Ty sc mp c hc hwt hfields hf hmem =>
    exact .union S n f f0Ty sc mp c hc hwt hfields hf (hmem.of_live_base hlive hbase)

/-- A memory-backed local related by `UnionLocalRel` points into a live
allocation. -/
theorem UnionLocalRel.indirect_allocId {mach : AnnealMachine} {decl : LocalDecl}
    {layouts : LayoutTable} {slot : LocalSlot} {mp : Miri.Interpreter.MemPlace AnnealProv}
    {c : Option Miri.Interpreter.LocalLayout}
    (h : UnionLocalRel mach decl layouts slot ⟨.live (.indirect mp), c⟩) :
    ∃ a la, mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some a ∧
      (a, la) ∈ mach.memory.live.toList := by
  cases h with
  | base _ _ hl =>
    cases hl with
    | indirect _ _ _ _ _ hmp =>
      obtain ⟨allocId, tag, _, _, localAlloc, hprov, _, _, hl, _⟩ := hmp
      exact ⟨allocId, localAlloc, by rw [hprov]; rfl, hl⟩
  | union _ _ _ _ _ _ _ _ _ _ _ hmem =>
    cases hmem with
    | mk allocId tag _ localAlloc _ hprov _ _ hl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact ⟨allocId, localAlloc, by rw [hprov]; rfl, hl⟩

theorem FrameRelLM2_4.indirect_allocId {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM2_4 body mach af mf) {j : Nat} {mp : Miri.Interpreter.MemPlace AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hj : mf.locals[j]? = some ⟨.live (.indirect mp), lay⟩) :
    ∃ a la, mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some a ∧
      (a, la) ∈ mach.memory.live.toList := by
  obtain ⟨hlt_j, _⟩ := Array.getElem?_eq_some_iff.mp hj
  have hlt_d : j < body.localDecls.length := by rw [← hfr.mf_locals_size]; exact hlt_j
  have hdecl : get? body.localDecls j = some (body.localDecls[j]'hlt_d) :=
    List.getElem?_eq_getElem hlt_d
  obtain ⟨slot, mls, _, _, _, hmls, _, hloc⟩ := hfr.lookup_local hdecl
  rw [hj] at hmls
  cases hmls
  exact hloc.indirect_allocId

/-- **Union aggregate** (`LM-2.4` + `D13a` active-field upgrade): the assignment
`_u = U { field_f: op }` (`Rvalue.aggregate (.adt d 0 (some f)) [op]` for ANY
valid field `f < n`) of a scalar constant or `copy` of an immediate scalar local
`op` of primitive type `f0Ty` (`k` bytes) into an uninitialized union local `_u`
of `S ≥ k` bytes.

Both machines step in lockstep (`StepRelLM2_4`): both report undefined behavior
when `op` reads an uninitialized or dead local, and otherwise both step to
related states. On a normal step, Anneal stores
`.aggregate 0 (unionSlotFields n f (.scalar sc))` (`evalAggregateAdtUnionValue?`)
and `lean-miri` moves `_u` into a fresh stack allocation, projects to field `f`
at offset `0`, writes `sc` into its bytes `[0, k)`, and leaves its bytes
`[k, S)` uninitialized (`UnionMemRel`, whose mask is `unionPrefixMask S k`). -/
theorem step_union_aggregate_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {u : Local} {d : DefPath} {f : Nat} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩)
    {uDecl : LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {S n : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl)
    (hfl_sized : fl.layout.isSized = true)
    (hu_uninit : get? s.frame.locals u = some .uninit)
    (hu_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame u)
    {f0Ty : Ty} (hprim0 : IsPrimScalarTy f0Ty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op f0Ty)
    (hf0_le : (translateTy f0Ty body.layouts).layout.size.bytes.toNat ≤ S)
    (hadt : ∃ args, uDecl.ty.kind = .adt d args := by exact ⟨_, rfl⟩)
    (hfl_sz : fl.layout.size = (translateTy f0Ty body.layouts).layout.size := by rfl)
    (hdecls_adt : ∀ l ∈ collectAdtLayoutsInDecls body.layouts d body.localDecls,
      body.layouts.lookup uDecl.ty.layoutIdx = some l := by
        simp [collectAdtLayoutsInDecls, collectAdtLayoutsInTyAux, stringEq,
          LayoutTable.lookup, get?]) :
    StepRelLM2_4 body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      ∃ (sc : MirAst.ScalarInt) (mp : Miri.Interpreter.MemPlace AnnealProv)
        (m' : AnnealStepState)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
          .ok (.scalar sc) s.frame.locals ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals u =
          some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) ∧
        m'.stack.frames = #[tf'] ∧
        (∃ c, tf'.locals[u]? = some ⟨.live (.indirect mp), c⟩) ∧
        UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty sc mp ∧
        LiveAllocsNodup m'.machine ∧
        (∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ u →
          IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
        (∀ j, j ≠ u → get? s'.frame.locals j = get? s.frame.locals j) ∧
        s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
        StepPreservesHighWater m 1 (m', .ok true)) := by
  rcases hstate with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  obtain ⟨mem', id, hres⟩ := hcanRes
  have hop_tf := hop topFrame hframes
  have hu_imm_tf := hu_imm topFrame hframes
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  have hrv_spec := evalRvalue_unionAggregate_activeField_eq (locals := s.frame.locals)
    hbor hcaller hdecl_u hadt hwt hfields hf hfl hprim0 hfl_sz hop_tf hdecls_adt
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩
      body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
  obtain ⟨slot_u, mls_u, hlt_af_u, hlt_u, hslot_u, hmls_u, hmls_u_eq, hloc_u⟩ :=
    hframe.lookup_local hdecl_u
  rw [hu_uninit] at hslot_u
  injection hslot_u with hslot_u
  subst hslot_u
  have hcache_u := hloc_u.layout_eq
  have hu_imm' := hu_imm_tf mls_u hmls_u
  have hmls_u_val : mls_u.value = .live (.immediate .uninit) := by
    cases hloc_u with
    | base _ _ hloc_u' =>
      cases hloc_u' with
      | indirect _ mp' _ _ _ _ => exact absurd rfl (hu_imm' mp')
      | immediate _ imm _ _ hv =>
        rcases hv with ⟨_, rfl⟩ | ⟨_, h, _⟩
        · rfl
        · cases h
  let lay := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame u hlt_u lay
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 u none topFrame.localsIdentity, lay⟩
  have hevalPlace : annealEvalPlace body.localDecls body.layouts ⟨u, #[]⟩ m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_u hdecl_u (by rw [hmls_u_eq]; exact hcache_u)
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hc₀ : (topFrame₀.locals[u]'hlt_u₀).layout = some lay := by
    simp [topFrame₀, cacheFrameLocalLayout]
  have hval₀ : (topFrame₀.locals[u]'hlt_u₀).value = .live (.immediate .uninit) := by
    simp [topFrame₀, cacheFrameLocalLayout, hmls_u_eq, hmls_u_val]
  obtain ⟨alloc, htry, hbs, hlen, hnat, hmut, hal, hprov, hmask⟩ :=
    freshUnionAlloc_spec lay.layout.size lay.layout.align.abi (translateTy_align_pow2_le_29 _ _)
  let mp := stackAllocPlace id
  let mach₁ := stackAllocMachine m.machine mem' id (alloc.withExtra none)
  let tf₁ := setFrameLocalIndirect topFrame₀ u hlt_u₀ mp
  have hfield : annealUnionAggregateField body.localDecls body.layouts destPlace f m₀ =
      .ok ⟨.memory mp, fl⟩ { stack := ⟨#[tf₁]⟩, machine := mach₁ } :=
    annealUnionAggregateField_fresh (body := body) (m := m₀) rfl hlt_u₀ hdecl_u hc₀ hval₀
      hfields hf hwt.sized hfl hfl_sized htry hres topFrame.localsIdentity
  have hframe₀ : FrameRelLM2_4 body m.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_u hlt_u
  have hop₀ : WellTypedScalarOperand body topFrame₀ op f0Ty := hop_tf.cache_layout hlt_u lay
  have hne : ∀ idx, op = .copy ⟨idx, .nil⟩ → idx ≠ u := by
    intro idx hidx
    subst hidx
    cases hop_tf with
    | copyLocal _ decl hdecl _ _ => exact primScalar_ne_union_local hdecl_u hwt hdecl hprim0
  have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
  have hunionLay : isUnionLayout destPlace.layout = true := by
    simp only [destPlace, isUnionLayout, lay, hfields]
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨u, #[]⟩
      (translateRvalue (.aggregate (.adt d 0 (some f)) [op])) = true := by
    simp [lm24Assign, lm24Place, hunion]
  have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
      ⟨u, #[]⟩ true m = .ok destPlace m₀ := hevalPlace
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.writeAggregate (annealAggregateHooksLM2_4 body.localDecls body.layouts) ()
          (.Adt 0 0 #[] none (some f)) #[translateOperand op] destPlace) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    dsimp only [translateRvalue, translateAggregateKind, List.map, List.toArray]
    rw [evalRvalueIntoPlace_aggregate_def]
    exact EStateM.bind_eq_ok hevalPlace'
  have hwa_pre : ∀ (k : Miri.Interpreter.RvalueM AnnealStepState Unit),
      (do
        let variantDest ← (annealAggregateHooksLM2_4 body.localDecls body.layouts).projectDowncast ()
          destPlace 0
        let field ← (annealAggregateHooksLM2_4 body.localDecls body.layouts).projectField ()
          variantDest f
        let operand ← (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
          (Miri.Interpreter.OperandPath.aggregate 0) (translateOperand op)
          (some ((annealAggregateHooksLM2_4 body.localDecls body.layouts).placeLayout field))
        (annealAggregateHooksLM2_4 body.localDecls body.layouts).copyOpNoValidate () operand
          field false
        k) m₀ =
      (do
        let operand ← (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
          (Miri.Interpreter.OperandPath.aggregate 0) (translateOperand op) (some fl)
        (annealAggregateHooksLM2_4 body.localDecls body.layouts).copyOpNoValidate () operand
          ⟨.memory mp, fl⟩ false
        k) { stack := ⟨#[tf₁]⟩, machine := mach₁ } := by
    intro k
    simp only [aggLM2_4_projectDowncast, hunionLay, ↓reduceIte, beq_self_eq_true,
      aggLM2_4_projectField, bind, EStateM.bind, pure, EStateM.pure, hfield]
    rfl
  rcases evalScalarOperand_union_dst (mach' := mach₁) hframe₀ hprim0 hop₀ hne hlt_u₀ mp
      s.memory.globals (.aggregate 0) (some fl) with
    ⟨ha_ub, m_err, msg, hm_err⟩ |
    ⟨sc, msc, tf₂, hlt₂, ha_ok, hm_ok, hframe₂, hdisj₂, hmono₂, htf₂, _, hrel, himmRel⟩
  · -- `op` reads an uninitialized or dead local: undefined behavior in both machines.
    have ha : evalStmt s ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only; rw [hrv_spec.1 ha_ub]
    have hm_err' : (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
        (Miri.Interpreter.OperandPath.aggregate 0) (translateOperand op) (some fl)
        { stack := ⟨#[tf₁]⟩, machine := mach₁ } = .error (.undefinedBehavior msg) m_err := hm_err
    have hwa : Miri.Interpreter.writeAggregate
        (annealAggregateHooksLM2_4 body.localDecls body.layouts) ()
        (.Adt 0 0 #[] none (some f)) #[translateOperand op] destPlace m₀ =
        .error (.undefinedBehavior msg) m_err := by
      rw [writeAggregate_union_def, hwa_pre, EStateM.bind_eq_error hm_err']
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩) m =
        (m_err, .error (.undefinedBehavior msg)) := by
      rw [hm_eval]
      unfold Miri.Interpreter.runRvalue
      rw [hwa]
    rw [hstep_a, ha, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_stmt]
    exact ⟨.ub _ _, fun _ h => absurd h MirStepNode_fail_ne_step⟩
  · -- `op` evaluates to `sc`: `lean-miri` writes it into the fresh allocation.
    obtain ⟨hsz_k, hkv⟩ : (translateTy f0Ty body.layouts).layout.size =
        translateSizeBytes sc.sizeBytes ∧ ValidScalarBytes sc.sizeBytes := by
      cases himmRel with
      | scalar _ _ hr hsz _ _ => exact ⟨hsz, hr.validBytes⟩
    have hk_le : sc.sizeBytes ≤ S := by
      have h := translateSizeBytes_toNat_of_valid hkv
      rw [hsz_k, h] at hf0_le
      exact hf0_le
    have hS := hwt.size_valid
    have hS16 : S ≤ 16 := by rcases hS with h | h | h | h | h <;> omega
    have hlay_sz : lay.layout.size = translateSizeBytes S := hwt.size_eq
    have hA_len : (alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).len = S := by
      show alloc.len = S
      rw [hlen, hlay_sz]
      exact translateSizeBytes_toNat_of_valid hS
    have hA_sz : (alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).byteSize =
        translateSizeBytes S := by
      show alloc.byteSize = _
      rw [hbs, hlay_sz]
    have hset : (alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).initializationMask.setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) true =
        .ok (unionPrefixMask S sc.sizeBytes) := by
      show alloc.initializationMask.setRange _ true = _
      rw [hmask, hlay_sz]
      exact unionPrefixMask_fresh hS hkv hk_le
    have hfresh : mem'.live.any (fun entry => entry.1 == id) = false := by
      have h := (reserveAllocId_ok_live hres).2
      rwa [← (reserveAllocId_ok_live hres).1] at h
    obtain ⟨A', hw, hA'_sz, hA'_len, hA'_align, hA'_mut, hA'_prov, hA'_mask, hA'_extra,
        hA'_native, hA'_raw⟩ :=
      annealWriteImmediate_unionFresh (mach := m.machine)
        (tf := setFrameLocalIndirect tf₂ u hlt₂ mp) (destLay := fl) hfresh hrel hA_len hA_sz hS16
        hk_le hmut hprov hset
    let mach₃ := stackAllocMachine m.machine mem' id A'
    let tf₃ := setFrameLocalIndirect tf₂ u hlt₂ mp
    let st₃ : AnnealStepState := { stack := ⟨#[tf₃]⟩, machine := mach₃ }
    have hm_ok' : (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
        (Miri.Interpreter.OperandPath.aggregate 0) (translateOperand op) (some fl)
        { stack := ⟨#[tf₁]⟩, machine := mach₁ } =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy f0Ty body.layouts⟩
          { stack := ⟨#[tf₃]⟩, machine := mach₁ } := hm_ok
    have hcopy : (annealAggregateHooksLM2_4 body.localDecls body.layouts).copyOpNoValidate ()
        ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy f0Ty body.layouts⟩
        ⟨.memory mp, fl⟩ false { stack := ⟨#[tf₃]⟩, machine := mach₁ } = .ok () st₃ := by
      rw [aggLM2_4_copyOpNoValidate]
      simp only [bind, EStateM.bind, annealReadImmediateLM2_2, pure, EStateM.pure]
      exact hw
    have hlt₃ : u < tf₃.locals.size := by
      dsimp only [tf₃, setFrameLocalIndirect]; rw [Array.size_set]; exact hlt₂
    have hu₃ : (tf₃.locals[u]'hlt₃).value = .live (.indirect mp) := by
      simp [tf₃, setFrameLocalIndirect]
    have hdisc : (annealAggregateHooksLM2_4 body.localDecls body.layouts).writeDiscriminant () 0
        destPlace st₃ = .ok () st₃ := by
      rw [aggLM2_4_writeDiscriminant]
      have hens : annealEnsureAllocated destPlace st₃ = .ok mp st₃ :=
        annealEnsureAllocated_indirect rfl hlt₃ hu₃
      rw [EStateM.bind_eq_ok hens]
      rfl
    have hwa : Miri.Interpreter.writeAggregate
        (annealAggregateHooksLM2_4 body.localDecls body.layouts) ()
        (.Adt 0 0 #[] none (some f)) #[translateOperand op] destPlace m₀ = .ok () st₃ := by
      rw [writeAggregate_union_def, hwa_pre, EStateM.bind_eq_ok hm_ok', EStateM.bind_eq_ok hcopy,
        EStateM.bind_eq_ok hdisc]
      simp only [aggLM2_4_enforceValidity, aggLM2_4_validate, bind, EStateM.bind, pure,
        EStateM.pure, ↓reduceIte]
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩) m =
        (st₃, .ok ()) := by
      rw [hm_eval]
      unfold Miri.Interpreter.runRvalue
      rw [hwa]
    have hloc₃ : tf₃.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
      show tf₂.location = _
      have h : tf₂.location = topFrame₀.location := by rw [htf₂]
      rw [h]
      exact hframe.location_eq
    have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
      hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl hloc₃
    -- Anneal: the union value `.aggregate 0 (unionSlotFields n f (.scalar sc))` is written into `_u`.
    have hrv := hrv_spec.2 sc msc ha_ok himmRel
    let locals₂ := s.frame.locals.set u (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))
    have ha_ok' : evalStmt s ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩
        body.localDecls body.layouts = MirStepNode.step (advanceStmt s locals₂ s.memory) := by
      unfold evalStmt
      dsimp only
      rw [hrv]
      simp only []
      rw [hprot, hbor]
      dsimp only [invalidateConflictingBorrows]
      rw [hmem_same]
      simp [hu_uninit, set?_eq_some_set hlt_af_u, locals₂]
    -- The post-state relation.
    let tf_fin := { tf₃ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
    let m' : AnnealStepState := { st₃ with stack := ⟨#[tf_fin]⟩ }
    have hmem_rel : UnionMemRel mach₃ uDecl.ty body.layouts S f0Ty sc mp :=
      .mk id .one (annealStackBaseAddr id) ⟨.stack, A'⟩ msc rfl rfl rfl
        (by simp [mach₃, stackAllocMachine])
        (lookupBaseAddr_stackAllocMachine_self _ _ _ _) rfl (annealStackBaseAddr_add_lt id hS16)
        (hA'_sz.trans hA_sz) hA'_len hA'_mut hA'_prov (hA'_align.trans hal) hA'_extra
        (hA'_native.trans hnat) hk_le (hA'_mask ▸ .of_fresh S sc.sizeBytes) hrel hprim0 himmRel hA'_raw
    have htf₂_body : tf₂.body = topFrame.body := by rw [htf₂]; rfl
    have htf₂_rc : tf₂.returnContinuation = topFrame.returnContinuation := by rw [htf₂]; rfl
    have htf₂_rp : tf₂.returnPlace = topFrame.returnPlace := by rw [htf₂]; rfl
    have htf₂_id : tf₂.localsIdentity = topFrame.localsIdentity := by rw [htf₂]; rfl
    obtain ⟨hlive_b, hfreshne, hbase_b⟩ := stackAllocMachine_live_base (mach := m.machine) A' hres
    have hframe_fin : FrameRelLM2_4 body mach₃ (advanceStmt s locals₂ s.memory).frame tf_fin :=
      { body_eq := by
          show tf₂.body = _
          rw [htf₂_body]
          exact hframe.body_eq
        location_eq := rfl
        af_locals_len := by
          show (s.frame.locals.set u _).length = _
          rw [List.length_set]
          exact hframe.af_locals_len
        mf_locals_size := by
          show (tf₂.locals.set u _ hlt₂).size = _
          rw [Array.size_set]
          exact hframe₂.mf_locals_size
        locals_rel := by
          intro i decl slot mls hdecl hslot hmls
          have hslot' : get? locals₂ i = some slot := hslot
          have hmls' : (tf₂.locals.set u
              { tf₂.locals[u]'hlt₂ with value := .live (.indirect mp) } hlt₂)[i]? = some mls := hmls
          rw [get?_eq_getElem?, List.getElem?_set] at hslot'
          rw [Array.getElem?_set] at hmls'
          by_cases hiu : u = i
          · subst hiu
            simp only [↓reduceIte, hlt_af_u, Option.some.injEq] at hslot' hmls'
            subst hslot' hmls'
            rw [hdecl_u] at hdecl
            cases hdecl
            have hloc₂ := hframe₂.locals_rel u uDecl .uninit (tf₂.locals[u]'hlt₂) hdecl_u
              hu_uninit (Array.getElem?_eq_getElem hlt₂)
            exact .union S n f f0Ty sc mp _ hloc₂.layout_eq hwt hfields hf hmem_rel
          · simp only [hiu, ↓reduceIte] at hslot' hmls'
            have hloc := hframe₂.locals_rel i decl slot mls hdecl hslot' hmls'
            exact hloc.of_live_base hlive_b hbase_b }
    have hdisj_fin : MemoryAllocDisjoint tf_fin := by
      have hdisj₂' : MemoryAllocDisjoint tf₂ := hdisj₂ (hdisj.cache_layout hlt_u lay)
      intro i j mp_i mp_j lay_i lay_j hij hi hj
      dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hi hj
      rw [Array.getElem?_set] at hi hj
      by_cases hi_u : u = i
      · subst hi_u
        have hj_u : u ≠ j := hij
        simp only [hj_u, ↓reduceIte] at hj
        simp only [↓reduceIte] at hi
        obtain ⟨a, la, ha, hla⟩ := hframe₂.indirect_allocId hj
        injection hi with hi
        injection hi with hv _
        injection hv with hv
        injection hv with hv
        subst hv
        rw [ha]
        simp only [mp, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
          Option.some.injEq]
        exact fun h => hfreshne a la hla h.symm
      · simp only [hi_u, ↓reduceIte] at hi
        by_cases hj_u : u = j
        · subst hj_u
          simp only [↓reduceIte] at hj
          obtain ⟨a, la, ha, hla⟩ := hframe₂.indirect_allocId hi
          injection hj with hj
          injection hj with hv _
          injection hv with hv
          injection hv with hv
          subst hv
          rw [ha]
          simp only [mp, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
            Option.some.injEq]
          exact hfreshne a la hla
        · simp only [hj_u, ↓reduceIte] at hj
          exact hdisj₂' i j mp_i mp_j lay_i lay_j hij hi hj
    have hstate' : StateRelLM2_4 body (advanceStmt s locals₂ s.memory) m' :=
      StateRelLM2_4.mk tf_fin rfl (by show tf₂.returnContinuation = _; rw [htf₂_rc]; exact hretCont)
        ⟨retLay, by
          show tf₂.returnPlace = .frameLocal 0 0 none retLay tf₂.localsIdentity
          rw [htf₂_rp, htf₂_id]
          exact hretPlace⟩
        hframe_fin hcal hstack hbor hprot hcaller hdisj_fin
    have himm_fin : ∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ u →
        IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf_fin j := by
      intro tf htf j hj himm_j
      rw [hframes] at htf
      have htf' : topFrame = tf := by simpa using htf
      subst htf'
      have h₂ := hmono₂ j (himm_j.cache_layout hlt_u lay)
      intro mls hmls
      dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hmls
      rw [Array.getElem?_set_ne _ (Ne.symm hj)] at hmls
      exact h₂ mls hmls
    rw [hstep_a, ha_ok', hstep_m]
    refine ⟨.step _ _ hstate', fun s' hs' => ?_⟩
    have hs'' := MirStepNode_step_inj hs'
    subst hs''
    refine ⟨sc, mp, m', tf_fin, rfl, ha_ok, hstate', ?_, rfl,
      ⟨(tf₂.locals[u]'hlt₂).layout, ?_⟩, hmem_rel, LiveAllocsNodup.stackAllocMachine A' hnodup hres,
      himm_fin, ?_, rfl, rfl, fun _ hw hb => MemoryHighWater.stackAllocMachine A' hw hb hres⟩
    · simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_u]
    · simp [tf_fin, tf₃, setFrameLocalIndirect]
    · intro j hj
      simp [advanceStmt, locals₂, get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hj)]

/-! ## 7. Whole-Union Copies (`union_whole_copy_initMask_preservation`) -/

/-- The initialization mask of a union related by `UnionMemRel` (the `I-11`
invariant): its allocation initializes exactly the bytes `[0, k)` of field `0`
(`k = sc.sizeBytes`), so the prefix `[0, k)` reads as initialized and the whole
union `[0, S)` reads as initialized exactly when `k = S`. -/
theorem UnionMemRel.initMask_spec {mach : AnnealMachine} {uTy : Ty} {layouts : LayoutTable}
    {S : Nat} {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : UnionMemRel mach uTy layouts S f0Ty sc mp) (hS : ValidScalarBytes S) :
    ∃ allocId tag localAlloc,
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      (allocId, localAlloc) ∈ mach.memory.live.toList ∧
      IsUnionPrefixMask S sc.sizeBytes localAlloc.allocation.initializationMask ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) =
        .ok (.ok ()) ∧
      (localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) = .ok (.ok ()) ↔
        sc.sizeBytes = S) ∧
      (∀ idx : Nat, idx < S →
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat idx)) =
          .ok (decide (idx < sc.sizeBytes))) := by
  cases h with
  | mk allocId tag _ localAlloc _ hprov _ _ hl _ _ _ _ _ _ _ _ _ _ hk hmask hrel _ _ _ =>
    refine ⟨allocId, tag, localAlloc, hprov, hl, hmask, ?_, ?_, ?_⟩
    · exact hmask.init hS hrel.validBytes hrel.validBytes hk (Nat.le_refl _)
    · exact hmask.whole_iff hS hrel.validBytes hk
    · intro idx hidx
      exact hmask.get_byte hS hrel.validBytes hk idx hidx

private theorem uint8_ofNat_mod_256 (y : Nat) : UInt8.ofNat (y % 256) = UInt8.ofNat y := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  simp

private theorem encodeLittleEndianBytes_range' (n : Nat) :
    ∀ (x k : Nat) (prov : Option (Nat × Nat)),
      encodeLittleEndianBytes (x / 2 ^ (8 * k)) n prov =
        (List.range' k n).map (fun i => .init (UInt8.ofNat ((x / 2 ^ (8 * i)) % 256)) prov) := by
  induction n with
  | zero => intro x k prov; rfl
  | succ n ih =>
    intro x k prov
    have hdiv : Nat.div (x / 2 ^ (8 * k)) 256 = x / 2 ^ (8 * (k + 1)) := by
      change (x / 2 ^ (8 * k)) / 256 = x / 2 ^ (8 * (k + 1))
      rw [Nat.div_div_eq_div_mul, show 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 by
        rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]]
    simp only [encodeLittleEndianBytes, List.range'_succ, List.map_cons, uint8_ofNat_mod_256,
      hdiv, ih x (k + 1) prov]

theorem encodeLittleEndianBytes_eq_allocLeBytes (x n : Nat) (prov : Option (Nat × Nat)) :
    encodeLittleEndianBytes x n prov =
      (allocLeBytes x n).toList.map (fun b => .init b prov) := by
  have h := encodeLittleEndianBytes_range' n x 0 prov
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h
  rw [h]
  simp [allocLeBytes, List.map_map, Function.comp]

theorem writeAbstractBytesAt_replicateUninitBytes_zero :
    ∀ (bs : List AbstractByte) (S : Nat),
      bs.length ≤ S →
      writeAbstractBytesAt (replicateUninitBytes S) 0 bs =
        some (bs ++ replicateUninitBytes (S - bs.length))
  | [], S, _ => by cases S <;> rfl
  | _ :: _, 0, h => by simp at h
  | b :: bs, S + 1, h => by
    simp only [List.length_cons, Nat.succ_sub_succ_eq_sub] at h ⊢
    show (match writeAbstractBytesAt (replicateUninitBytes S) 0 bs with
      | some tail' => some (b :: tail')
      | none => none) = _
    rw [writeAbstractBytesAt_replicateUninitBytes_zero bs S (by omega)]
    rfl

/-- Anneal's byte-level union encoder `encodeUnionFieldsWith` on a single scalar
field `sc` of `k = sc.sizeBytes ≤ S` bytes agrees byte for byte with
`lean-miri`'s union allocation (`UnionMemRel`): bytes `[0, k)` are
`.init b none` matching `unionAllocRaw`, bytes `[k, S)` are `.uninit`, and for
every byte index `idx < S`, `InitMask.get` returns `.ok ab.isInit`. -/
theorem encodeUnionFieldsWith_matches_unionMemRel
    {mach : AnnealMachine} {uTy : Ty} {layouts : LayoutTable}
    {S : Nat} {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : UnionMemRel mach uTy layouts S f0Ty sc mp) (hS : ValidScalarBytes S) :
    let bs := (allocLeBytes sc.bits sc.sizeBytes).toList.map (fun b => AbstractByte.init b none) ++
      replicateUninitBytes (S - sc.sizeBytes)
    encodeUnionFieldsWith (encodeUntypedValueToBytes 1) S [.scalar sc] = some bs ∧
    bs.length = S ∧
    ∃ allocId tag localAlloc,
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      (allocId, localAlloc) ∈ mach.memory.live.toList ∧
      ∃ hraw_len : (unionAllocRaw localAlloc.allocation).size = S,
        ∀ idx : Nat, (hidx : idx < S) →
          ∃ ab : AbstractByte,
            get? bs idx = some ab ∧
            ab.isInit = decide (idx < sc.sizeBytes) ∧
            localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat idx)) =
              .ok ab.isInit ∧
            (idx < sc.sizeBytes →
              ab = .init ((unionAllocRaw localAlloc.allocation)[idx]'(by omega)) none) := by
  intro bs
  cases h with
  | mk allocId tag _ localAlloc _ hprov _ _ hl _ _ _ _ hlen _ _ _ _ _ hk hmask hrel _ _ hraw =>
    have hkv := hrel.validBytes
    have hbeq0 : Nat.beq sc.sizeBytes 0 = false := by
      rcases hkv with h | h | h | h | h <;> rw [h] <;> rfl
    let fbs := (allocLeBytes sc.bits sc.sizeBytes).toList.map (fun b => AbstractByte.init b none)
    have hfbs_len : fbs.length = sc.sizeBytes := by
      simp [fbs, allocLeBytes]
    have hfbs_len' : length fbs = sc.sizeBytes := hfbs_len
    have henc_sc : encodeUntypedValueToBytes 1 (.scalar sc) = some fbs := by
      simp [encodeUntypedValueToBytes, encodeScalarBytes, hbeq0,
        encodeLittleEndianBytes_eq_allocLeBytes, fbs]
    have hwrite : writeAbstractBytesAt (replicateUninitBytes S) 0 fbs = some bs := by
      simpa [bs, fbs, hfbs_len] using
        writeAbstractBytesAt_replicateUninitBytes_zero fbs S (by omega)
    have henc : encodeUnionFieldsWith (encodeUntypedValueToBytes 1) S [.scalar sc] = some bs := by
      unfold encodeUnionFieldsWith encodeUnionFieldsWith.findFullSize
      dsimp only
      rw [henc_sc]
      simp only [hfbs_len', hwrite]
      cases Nat.beq sc.sizeBytes S with
      | true => rfl
      | false =>
        simp only [hbeq0]
    have hbs_len : bs.length = S := by
      simp [bs, fbs, hfbs_len, replicateUninitBytes_eq_replicate]
      omega
    have hraw_len : (unionAllocRaw localAlloc.allocation).size = S := hlen
    refine ⟨henc, hbs_len, allocId, tag, localAlloc, hprov, hl, hraw_len, ?_⟩
    intro idx hidx
    rw [get?_eq_getElem?]
    by_cases hlt : idx < sc.sizeBytes
    · have hlt_fbs : idx < fbs.length := by omega
      have hget_bs : bs[idx]? = some (fbs[idx]'hlt_fbs) := by
        dsimp only [bs]
        rw [List.getElem?_append_left hlt_fbs, List.getElem?_eq_getElem hlt_fbs]
      have hfbs_elem : fbs[idx]'hlt_fbs =
          .init ((allocLeBytes sc.bits sc.sizeBytes)[idx]'(by simp [allocLeBytes_size, hlt])) none := by
        simp [fbs]
      have hextr : ((unionAllocRaw localAlloc.allocation).extract 0 sc.sizeBytes)[idx]? =
          some ((allocLeBytes sc.bits sc.sizeBytes)[idx]'(by simp [allocLeBytes_size, hlt])) := by
        rw [hraw, Array.getElem?_eq_getElem]
      have hmin : idx < min sc.sizeBytes (unionAllocRaw localAlloc.allocation).size := by omega
      have hextr' : ((unionAllocRaw localAlloc.allocation).extract 0 sc.sizeBytes)[idx]? =
          some ((unionAllocRaw localAlloc.allocation)[idx]'(by omega)) := by
        rw [Array.getElem?_extract]
        simp [hmin, Array.getElem?_eq_getElem (by omega : idx < (unionAllocRaw localAlloc.allocation).size)]
      have hbyte_eq : (allocLeBytes sc.bits sc.sizeBytes)[idx]'(by simp [allocLeBytes_size, hlt]) =
          (unionAllocRaw localAlloc.allocation)[idx]'(by omega) :=
        Option.some.inj (hextr.symm.trans hextr')
      refine ⟨fbs[idx]'hlt_fbs, hget_bs, ?_, ?_, fun _ => hfbs_elem.trans (by rw [hbyte_eq])⟩
      · rw [hfbs_elem]; simp [AbstractByte.isInit, hlt]
      · rw [hfbs_elem]
        simp only [AbstractByte.isInit]
        simpa [hlt] using hmask.get_byte hS hkv hk idx hidx
    · have hge_fbs : fbs.length ≤ idx := by omega
      have hget_bs : bs[idx]? = some .uninit := by
        dsimp only [bs]
        rw [List.getElem?_append_right hge_fbs, replicateUninitBytes_eq_replicate,
          List.getElem?_replicate]
        have : idx - fbs.length < S - sc.sizeBytes := by omega
        simp [this]
      refine ⟨.uninit, hget_bs, ?_, ?_, fun h => absurd h hlt⟩
      · simp [AbstractByte.isInit, hlt]
      · simp only [AbstractByte.isInit]
        simpa [hlt] using hmask.get_byte hS hkv hk idx hidx

/-- `annealMemCopyOp` from a memory-backed union (allocation `allocId`, at its
offset `0`) into an uninitialized immediate union local `w` of the same size
and alignment: `w` moves into the fresh allocation `id`, which is then populated
by running `Miri.Memory.Allocation.copy` (`copyRepeatedly ... 1 ...`) from the
source allocation. -/
theorem annealMemCopyOp_freshUnion
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {w : Nat} {wDecl : LocalDecl} (hlt : w < tf.locals.size)
    (hdecl : get? body.localDecls w = some wDecl)
    (hc : (tf.locals[w]'hlt).layout = some (translateTy wDecl.ty body.layouts))
    (hval : (tf.locals[w]'hlt).value = .live (.immediate .uninit))
    (hsized : (translateTy wDecl.ty body.layouts).layout.isSized = true)
    {alloc : Miri.Memory.Allocation AnnealProv Unit}
    (htry : Miri.Memory.Allocation.tryNew (translateTy wDecl.ty body.layouts).layout.size
      (translateTy wDecl.ty body.layouts).layout.align.abi .Uninit annealZeroedStorage = .ok alloc)
    {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id))
    (hnodup : LiveAllocsNodup m.machine)
    {mp : Miri.Interpreter.MemPlace AnnealProv} {allocId : Miri.Memory.AllocId}
    {tag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {la : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hlive : (allocId, la) ∈ m.machine.memory.live.toList)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    {dest' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hcopy : Miri.Memory.Allocation.copy la.allocation
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy wDecl.ty body.layouts).layout.size)
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true (alloc.withExtra none) =
        .ok () dest')
    (srcLay : Miri.Interpreter.LocalLayout) (ident : Miri.Interpreter.LocalsIdentity) :
    annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp, srcLay⟩
        ⟨.local 0 w none ident, translateTy wDecl.ty body.layouts⟩ m =
      .ok () { stack := ⟨#[setFrameLocalIndirect tf w hlt (stackAllocPlace id)]⟩,
               machine := stackAllocMachine m.machine mem' id dest' } := by
  have hcf := cacheFrameLocalLayout_of_cached tf hlt hc
  have hlt' : w < (cacheFrameLocalLayout tf w hlt (translateTy wDecl.ty body.layouts)).locals.size :=
    by rw [hcf]; exact hlt
  have hforce := annealForceUnionAllocation_of_ok (forceAllocation_uninit_eq (body := body) hframes hlt
    hdecl (fun l hl => by rw [hc] at hl; exact (Option.some.inj hl).symm) hval hsized htry hres
    ident (translateTy wDecl.ty body.layouts) hlt')
  rw [setFrameLocalIndirect_congr hcf hlt' hlt] at hforce
  obtain ⟨hlive_b, hfreshne, hbase_b⟩ :=
    stackAllocMachine_live_base (mach := m.machine) (alloc.withExtra none) hres
  have hne : allocId ≠ id := hfreshne allocId la hlive
  have hnodup₂ := LiveAllocsNodup.stackAllocMachine (alloc.withExtra none) hnodup hres
  have hfind := array_find?_of_nodup_fst hnodup₂ (hlive_b _ hlive)
  have hbase₂ : (stackAllocMachine m.machine mem' id (alloc.withExtra none)).lookupBaseAddr
      allocId = some baseAddr := by
    rw [hbase_b _ _ hlive]; exact hbase
  have hbase_id := lookupBaseAddr_stackAllocMachine_self m.machine mem' id (alloc.withExtra none)
  have hfresh : mem'.live.any (fun entry => entry.1 == id) = false := by
    have h := (reserveAllocId_ok_live hres).2
    rwa [← (reserveAllocId_ok_live hres).1] at h
  have hidx := findIdx?_push_fresh mem'.live id
    ({ kind := .stack, allocation := alloc.withExtra none } : Miri.Memory.LocalAllocation
      AnnealProv (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind) hfresh
  have hlive₂ : (stackAllocMachine m.machine mem' id (alloc.withExtra none)).memory.live =
      mem'.live.push (id, ⟨.stack, alloc.withExtra none⟩) := rfl
  have hfind' : (mem'.live.push (id, ⟨.stack, alloc.withExtra none⟩)).find?
      (fun x => x.fst == allocId) = some (allocId, la) := hfind
  have hsrcOff : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = Miri.ABI.Size.ZERO := by
    rw [hptr]; simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
  have hdestOff : Miri.ABI.Size.ofBytes
      ((Miri.ABI.Size.ofBytes (annealStackBaseAddr id)).bytes - annealStackBaseAddr id) =
      Miri.ABI.Size.ZERO := by
    simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
  have hbeqf : (allocId == id) = false := beq_false_of_ne hne
  have hsz_nz : ((translateTy wDecl.ty body.layouts).layout.size.bytes == 0) = false := by
    cases h0 : ((translateTy wDecl.ty body.layouts).layout.size.bytes == 0) with
    | false => rfl
    | true =>
      unfold Miri.Memory.Allocation.copy Miri.Memory.Allocation.copyRepeatedly at hcopy
      dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hcopy
      split at hcopy
      · cases hcopy
      · split at hcopy
        · split at hcopy
          · cases hcopy
          · split at hcopy
            · unfold Miri.Memory.InitMask.prepareCopy at hcopy
              simp only [Miri.Memory.allocRange, h0, ↓reduceIte, throw, throwThe,
                MonadExceptOf.throw, bind, Except.bind] at hcopy
              cases hcopy
            · cases hcopy
        · cases hcopy
  unfold annealMemCopyOp
  simp only [bind, EStateM.bind, hforce, get, getThe, MonadStateOf.get, EStateM.get, hprov,
    Option.bind, Miri.Memory.Provenance.getAllocId, hbase₂, stackAllocPlace, hbase_id,
    hlive₂, hfind', hidx, Array.getElem?_push_size, hsrcOff, hdestOff, hsz_nz, Bool.false_eq_true,
    ↓reduceIte, hbeqf, hcopy, set, MonadStateOf.set, array_push_set!_size]
  rfl

/-- **`union_whole_copy_initMask_preservation_simulation`** (`LM-2.4`,
certifying `difftest-repair` `I-11`): `_w = copy _u`, where `_u` is a union of
`S` bytes holding field `0`'s value `sc` (`k = sc.sizeBytes` initialized bytes,
`UnionMemRel`) and `_w` is an uninitialized local of the same union type.

Neither machine reports undefined behavior, even when `k < S`: both step, Anneal
copies the union value, and `lean-miri` moves `_w` into a fresh allocation and
copies `_u`'s allocation into it byte for byte and chunk by chunk via the
vendored `Miri.Memory.Allocation.copy` (`InitMask.prepareCopy` /
`prepareForOverwrite` / `applyCopy` in `annealMemCopyOp`). Afterwards `_u` and
`_w` satisfy `UnionMemRel` with the same `S` and `sc` (`IsUnionPrefixMask S k`),
so the initialized chunk `[0, k)` is preserved, and the uninitialized padding
`[k, S)` was neither required to be initialized nor initialized by the copy
(`UnionMemRel.initMask_spec`). -/
theorem union_whole_copy_initMask_preservation_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {w u : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩)
    {wDecl uDecl : LocalDecl} (hdecl_w : get? body.localDecls w = some wDecl)
    (hdecl_u : get? body.localDecls u = some uDecl) (hty : wDecl.ty = uDecl.ty)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields_u : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hw_uninit : get? s.frame.locals w = some .uninit)
    (hw_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame w) :
    ∃ (s' : MachineState) (m' : AnnealStepState) (mp_w : Miri.Interpreter.MemPlace AnnealProv)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      stepMirFn body s = .step s' ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      StateRelLM2_4 body s' m' ∧
      get? s'.frame.locals w =
        some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) ∧
      (∀ j, j ≠ w → get? s'.frame.locals j = get? s.frame.locals j) ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c, tf'.locals[w]? = some ⟨.live (.indirect mp_w), c⟩) ∧
      (∃ c, tf'.locals[u]? = some ⟨.live (.indirect mp), c⟩) ∧
      UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty sc mp ∧
      UnionMemRel m'.machine wDecl.ty body.layouts S f0Ty sc mp_w ∧
      LiveAllocsNodup m'.machine ∧
      (∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ w →
        IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
      s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
      StepPreservesHighWater m 1 (m', .ok true) := by
  rcases hstate with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  obtain ⟨mem', id, hres⟩ := hcanRes
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩ body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
  have hwu : w ≠ u := by
    intro h
    subst h
    rw [hw_uninit] at hu_slot
    cases hu_slot
  have hwt_w : WellTypedUnionTy body.layouts wDecl.ty S := hty ▸ hwt
  have hfields_w : (translateTy wDecl.ty body.layouts).layout.fields = .Union n := hty ▸ hfields_u
  have hS := hwt.size_valid
  have hS16 : S ≤ 16 := by rcases hS with h | h | h | h | h <;> omega
  obtain ⟨c_u, hmls_u⟩ := hu_mls topFrame hframes
  -- The destination `_w`: an uninitialized immediate.
  obtain ⟨slot_w, mls_w, hlt_af_w, hlt_w, hslot_w, hmls_w, hmls_w_eq, hloc_w⟩ :=
    hframe.lookup_local hdecl_w
  rw [hw_uninit] at hslot_w
  injection hslot_w with hslot_w
  subst hslot_w
  have hw_imm' := hw_imm topFrame hframes mls_w hmls_w
  have hloc_w' : LocalRel m.machine wDecl body.layouts .uninit mls_w := by
    cases hloc_w with
    | base _ _ hl => exact hl
  have hcache_w := hloc_w'.layout_eq
  have hmls_w_val : mls_w.value = .live (.immediate .uninit) := by
    cases hloc_w' with
    | indirect _ mp' _ _ _ _ => exact absurd rfl (hw_imm' mp')
    | immediate _ imm _ _ hv =>
      rcases hv with ⟨_, rfl⟩ | ⟨_, h, _⟩
      · rfl
      · cases h
  -- The source `_u`: memory-backed.
  obtain ⟨_, mls_u, _, hlt_u, _, hmls_u', hmls_u_eq, hloc_u⟩ := hframe.lookup_local hdecl_u
  rw [hmls_u] at hmls_u'
  injection hmls_u' with hmls_u'
  subst hmls_u'
  have hcache_u := hloc_u.layout_eq
  let layW := translateTy wDecl.ty body.layouts
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame w hlt_w layW
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 w none topFrame.localsIdentity, layW⟩
  have hevalPlace : annealEvalPlace body.localDecls body.layouts ⟨w, #[]⟩ m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_w hdecl_w (by rw [hmls_w_eq]; exact hcache_w)
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hmls_u₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp), c_u⟩ := by
    have h := Array.getElem?_eq_getElem hlt_u₀
    dsimp only [topFrame₀, cacheFrameLocalLayout] at h ⊢
    rw [Array.getElem?_set_ne _ hwu] at h
    rw [hmls_u] at h
    exact (Option.some.inj h).symm
  let topFrame₁ := cacheFrameLocalLayout topFrame₀ u hlt_u₀ layU
  let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
  have hop : annealEvalOperand body.localDecls body.layouts (.Copy ⟨u, #[]⟩) (some layW) m₀ =
      .ok ⟨.indirect mp, layU⟩ m₁ :=
    annealEvalOperand_copy_live (m := m₀) rfl hlt_u₀ hdecl_u hmls_u₀ hcache_u
  have hlt_w₁ : w < topFrame₁.locals.size := by
    dsimp only [topFrame₁, topFrame₀]; rw [cacheFrameLocalLayout_size, cacheFrameLocalLayout_size]
    exact hlt_w
  have hmls_w₁ : topFrame₁.locals[w]? = some { mls_w with layout := some layW } := by
    dsimp only [topFrame₁, topFrame₀, cacheFrameLocalLayout]
    simp [Ne.symm hwu, hmls_w_eq]
  have hw₁ : topFrame₁.locals[w]'hlt_w₁ = { mls_w with layout := some layW } := by
    have h := Array.getElem?_eq_getElem hlt_w₁
    rw [hmls_w₁] at h
    exact (Option.some.inj h).symm
  have hc_w₁ : (topFrame₁.locals[w]'hlt_w₁).layout = some layW := by rw [hw₁]
  have hval_w₁ : (topFrame₁.locals[w]'hlt_w₁).value = .live (.immediate .uninit) := by
    rw [hw₁]; exact hmls_w_val
  obtain ⟨alloc, htry, hbs, _, hnat, hmut, hal, hprov_alloc, hmask_alloc⟩ :=
    freshUnionAlloc_spec layW.layout.size layW.layout.align.abi (translateTy_align_pow2_le_29 _ _)
  have hraw_alloc := tryNew_uninit_raw layW.layout.size layW.layout.align.abi alloc htry
  have hmem_orig := hmem
  cases hmem with
  | mk allocId tag baseAddr la msc hprov_u hmis_u hmeta_u hlive_u hbase_u hptr_u hovf_u hsz_u
      hlen_u hmut_u hp_u hal_u hex_u hnat_u hk hmask_u hrel hprim hf0imm hraw_u =>
  have hlayW_sz : layW.layout.size = translateSizeBytes S := hwt_w.size_eq
  have hlayW_toNat : layW.layout.size.bytes.toNat = S := by
    rw [hlayW_sz]
    exact translateSizeBytes_toNat_of_valid hS
  obtain ⟨A_w, hcopy_w, hA_sz, hA_len, hA_align, hA_mut, hA_prov, _, hA_mask_pred,
      hA_extra, hA_native, hA_raw⟩ :=
    union_copy_freshAlloc_spec (src := la.allocation)
      (dest := alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree))
      hS hrel.validBytes hk hlen_u hsz_u hp_u hmask_u
      (by show unionAllocRaw alloc = Array.replicate S 0; rw [hraw_alloc, hlayW_toNat])
      (by show alloc.byteSize = translateSizeBytes S; rw [hbs, hlayW_sz])
      hmut hprov_alloc
      (by show alloc.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes S) false
          rw [hmask_alloc, hlayW_sz])
  have hcopy_w' : Miri.Memory.Allocation.copy la.allocation
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO layW.layout.size)
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true (alloc.withExtra none) =
        .ok () A_w := by
    rw [hlayW_sz]
    exact hcopy_w
  have hmemcopy := annealMemCopyOp_freshUnion (body := body) (m := m₁) rfl hlt_w₁ hdecl_w hc_w₁
    hval_w₁ hwt_w.sized htry hres hnodup hprov_u hlive_u hbase_u hptr_u hcopy_w'
    layU topFrame.localsIdentity
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨w, #[]⟩
      (translateRvalue (.use (.copy ⟨u, .nil⟩))) = true := by
    have hunion := isUnionLocal_of_wellTyped hdecl_w hwt_w
    simp [lm24Assign, lm24Place, hunion]
  have huse : usesMemCopy ⟨.indirect mp, layU⟩ = true := by
    simp [usesMemCopy, layU, hfields_u]
  have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
      ⟨w, #[]⟩ true m = .ok destPlace m₀ := hevalPlace
  have hop' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.copy ⟨u, .nil⟩))
      (some ((annealRvalueHooksLM2_4 body.localDecls body.layouts).placeLayout destPlace)) m₀ =
      .ok ⟨.indirect mp, layU⟩ m₁ := hop
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp, layU⟩ destPlace) m₁ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace']
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop']
    simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2, huse, ↓reduceIte]
  let mp_w := stackAllocPlace id
  let mach₃ := stackAllocMachine m.machine mem' id A_w
  let tf₃ := setFrameLocalIndirect topFrame₁ w hlt_w₁ mp_w
  let st₃ : AnnealStepState := { stack := ⟨#[tf₃]⟩, machine := mach₃ }
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩) m = (st₃, .ok ()) := by
    rw [hm_eval]
    unfold Miri.Interpreter.runRvalue
    rw [hmemcopy]
  have hloc₃ : tf₃.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hframe.location_eq
  have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
    hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl hloc₃
  -- Anneal: `_w` receives the union value.
  have hvld := validateLoadedValue_unionWhole_true hdecl_u hwt false
    (.aggregate 0 (unionSlotFields n f (.scalar sc)))
  simp only [↓reduceIte, Bool.false_eq_true] at hvld
  have hrv : evalRvalue s.frame.locals (.use (.copy ⟨u, .nil⟩)) s.memory body.localDecls
      body.layouts =
      .ok (.aggregate 0 (unionSlotFields n f (.scalar sc))) s.frame.locals s.memory := by
    unfold evalRvalue; dsimp only; rw [hbor, hcaller]
    simp only [evalOperand, hu_slot, readProjectedValue, hvld]
  let locals₂ := s.frame.locals.set w (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))
  have ha_ok : evalStmt s ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩
      body.localDecls body.layouts = MirStepNode.step (advanceStmt s locals₂ s.memory) := by
    unfold evalStmt
    dsimp only
    rw [hrv]
    simp only []
    rw [hprot, hbor]
    dsimp only [invalidateConflictingBorrows]
    rw [hmem_same]
    simp [hw_uninit, set?_eq_some_set hlt_af_w, locals₂]
  -- The post-state relation.
  obtain ⟨hlive_b, hfreshne, hbase_b⟩ := stackAllocMachine_live_base (mach := m.machine) A_w hres
  have hmem_w : UnionMemRel mach₃ wDecl.ty body.layouts S f0Ty sc mp_w :=
    .mk id .one (annealStackBaseAddr id) ⟨.stack, A_w⟩ msc rfl rfl rfl
      (by simp [mach₃, stackAllocMachine])
      (lookupBaseAddr_stackAllocMachine_self _ _ _ _) rfl (annealStackBaseAddr_add_lt id hS16)
      hA_sz hA_len hA_mut hA_prov
      (by rw [hA_align]; exact hal) hA_extra (by rw [hA_native]; exact hnat) hk hA_mask_pred hrel
      hprim hf0imm (by rw [hA_raw]; exact hraw_u)
  have hmem_u : UnionMemRel mach₃ uDecl.ty body.layouts S f0Ty sc mp :=
    hmem_orig.of_live_base hlive_b hbase_b
  have hframe₁ : FrameRelLM2_4 body m.machine s.frame topFrame₁ :=
    (hframe.cache_local_layout hdecl_w hlt_w).cache_local_layout hdecl_u hlt_u₀
  have hdisj₁ : MemoryAllocDisjoint topFrame₁ :=
    (hdisj.cache_layout hlt_w _).cache_layout hlt_u₀ _
  let tf_fin := { tf₃ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
  let m' : AnnealStepState := { st₃ with stack := ⟨#[tf_fin]⟩ }
  have hframe_fin : FrameRelLM2_4 body mach₃ (advanceStmt s locals₂ s.memory).frame tf_fin :=
    { body_eq := hframe.body_eq
      location_eq := rfl
      af_locals_len := by
        show (s.frame.locals.set w _).length = _
        rw [List.length_set]
        exact hframe.af_locals_len
      mf_locals_size := by
        show (topFrame₁.locals.set w _ hlt_w₁).size = _
        rw [Array.size_set]
        exact hframe₁.mf_locals_size
      locals_rel := by
        intro i decl slot mls hdecl hslot hmls
        have hslot' : get? locals₂ i = some slot := hslot
        have hmls' : (topFrame₁.locals.set w
            { topFrame₁.locals[w]'hlt_w₁ with value := .live (.indirect mp_w) } hlt_w₁)[i]? =
            some mls := hmls
        rw [get?_eq_getElem?, List.getElem?_set] at hslot'
        rw [Array.getElem?_set] at hmls'
        by_cases hiw : w = i
        · subst hiw
          simp only [↓reduceIte, hlt_af_w, Option.some.injEq] at hslot' hmls'
          subst hslot' hmls'
          rw [hdecl_w] at hdecl
          cases hdecl
          refine .union S n f f0Ty sc mp_w _ ?_ hwt_w hfields_w hf hmem_w
          intro l hl
          rw [hc_w₁] at hl
          exact (Option.some.inj hl).symm
        · simp only [hiw, ↓reduceIte] at hslot' hmls'
          exact (hframe₁.locals_rel i decl slot mls hdecl hslot' hmls').of_live_base hlive_b
            hbase_b }
  have hdisj_fin : MemoryAllocDisjoint tf_fin := by
    intro i j mp_i mp_j lay_i lay_j hij hi hj
    dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hi hj
    rw [Array.getElem?_set] at hi hj
    by_cases hi_w : w = i
    · subst hi_w
      have hj_w : w ≠ j := hij
      simp only [hj_w, ↓reduceIte] at hj
      simp only [↓reduceIte] at hi
      obtain ⟨a, la', ha, hla⟩ := hframe₁.indirect_allocId hj
      injection hi with hi
      injection hi with hv _
      injection hv with hv
      injection hv with hv
      subst hv
      rw [ha]
      simp only [mp_w, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
        Option.some.injEq]
      exact fun h => hfreshne a la' hla h.symm
    · simp only [hi_w, ↓reduceIte] at hi
      by_cases hj_w : w = j
      · subst hj_w
        simp only [↓reduceIte] at hj
        obtain ⟨a, la', ha, hla⟩ := hframe₁.indirect_allocId hi
        injection hj with hj
        injection hj with hv _
        injection hv with hv
        injection hv with hv
        subst hv
        rw [ha]
        simp only [mp_w, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
          Option.some.injEq]
        exact hfreshne a la' hla
      · simp only [hj_w, ↓reduceIte] at hj
        exact hdisj₁ i j mp_i mp_j lay_i lay_j hij hi hj
  have hstate' : StateRelLM2_4 body (advanceStmt s locals₂ s.memory) m' :=
    StateRelLM2_4.mk tf_fin rfl hretCont ⟨retLay, hretPlace⟩ hframe_fin hcal hstack hbor hprot
      hcaller hdisj_fin
  have himm_fin : ∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ w →
      IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf_fin j := by
    intro tf htf j hj himm_j
    rw [hframes] at htf
    have htf' : topFrame = tf := by simpa using htf
    subst htf'
    have h₁ := (himm_j.cache_layout hlt_w layW).cache_layout hlt_u₀ layU
    intro mls hmls
    dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hmls
    rw [Array.getElem?_set_ne _ (Ne.symm hj)] at hmls
    exact h₁ mls hmls
  refine ⟨advanceStmt s locals₂ s.memory, m', mp_w, tf_fin, by rw [hstep_a, ha_ok],
    hstep_m, hstate', ?_, ?_, rfl, ⟨(topFrame₁.locals[w]'hlt_w₁).layout, ?_⟩,
    ⟨some layU, ?_⟩, hmem_u, hmem_w, LiveAllocsNodup.stackAllocMachine A_w hnodup hres,
    himm_fin, rfl, rfl, fun _ hw hb => MemoryHighWater.stackAllocMachine A_w hw hb hres⟩
  · simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_w]
  · intro j hj
    simp [advanceStmt, locals₂, get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hj)]
  · simp [tf_fin, tf₃, setFrameLocalIndirect]
  · dsimp only [tf_fin, tf₃, setFrameLocalIndirect]
    rw [Array.getElem?_set_ne _ hwu]
    dsimp only [topFrame₁, cacheFrameLocalLayout]
    rw [Array.getElem?_set_self, hmls_u₀]

/-- **`union_whole_move_initMask_preservation_simulation`** (`LM-2.4`):
`_w = move _u`, where `_u` is a union of `S` bytes holding active field `f`'s
value `sc` (`k = sc.sizeBytes` initialized bytes, `UnionMemRel`) and `_w` is an
uninitialized local of the same union type. -/
theorem union_whole_move_initMask_preservation_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {w u : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨w, .nil⟩ (.use (.move ⟨u, .nil⟩)), span⟩)
    {wDecl uDecl : LocalDecl} (hdecl_w : get? body.localDecls w = some wDecl)
    (hdecl_u : get? body.localDecls u = some uDecl) (hty : wDecl.ty = uDecl.ty)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields_u : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hw_uninit : get? s.frame.locals w = some .uninit)
    (hw_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame w) :
    ∃ (s' : MachineState) (m' : AnnealStepState) (mp_w : Miri.Interpreter.MemPlace AnnealProv)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      stepMirFn body s = .step s' ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      StateRelLM2_4 body s' m' ∧
      get? s'.frame.locals w =
        some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) ∧
      get? s'.frame.locals u = some .uninit ∧
      (∀ j, j ≠ w → j ≠ u → get? s'.frame.locals j = get? s.frame.locals j) ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c, tf'.locals[w]? = some ⟨.live (.indirect mp_w), c⟩) ∧
      (∃ c, tf'.locals[u]? = some ⟨.live (.immediate .uninit), c⟩) ∧
      UnionMemRel m'.machine wDecl.ty body.layouts S f0Ty sc mp_w ∧
      LiveAllocsNodup m'.machine ∧
      IsImmediateFrameLocal tf' u ∧
      (∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ w →
        IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
      s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
      StepPreservesHighWater m 1 (m', .ok true) := by
  rcases hstate with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  obtain ⟨mem', id, hres⟩ := hcanRes
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨w, .nil⟩ (.use (.move ⟨u, .nil⟩)), span⟩ body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
  have hwu : w ≠ u := by
    intro h
    subst h
    rw [hw_uninit] at hu_slot
    cases hu_slot
  have hwt_w : WellTypedUnionTy body.layouts wDecl.ty S := hty ▸ hwt
  have hfields_w : (translateTy wDecl.ty body.layouts).layout.fields = .Union n := hty ▸ hfields_u
  have hS := hwt.size_valid
  have hS16 : S ≤ 16 := by rcases hS with h | h | h | h | h <;> omega
  obtain ⟨c_u, hmls_u⟩ := hu_mls topFrame hframes
  obtain ⟨slot_w, mls_w, hlt_af_w, hlt_w, hslot_w, hmls_w, hmls_w_eq, hloc_w⟩ :=
    hframe.lookup_local hdecl_w
  rw [hw_uninit] at hslot_w
  injection hslot_w with hslot_w
  subst hslot_w
  have hw_imm' := hw_imm topFrame hframes mls_w hmls_w
  have hloc_w' : LocalRel m.machine wDecl body.layouts .uninit mls_w := by
    cases hloc_w with
    | base _ _ hl => exact hl
  have hcache_w := hloc_w'.layout_eq
  have hmls_w_val : mls_w.value = .live (.immediate .uninit) := by
    cases hloc_w' with
    | indirect _ mp' _ _ _ _ => exact absurd rfl (hw_imm' mp')
    | immediate _ imm _ _ hv =>
      rcases hv with ⟨_, rfl⟩ | ⟨_, h, _⟩
      · rfl
      · cases h
  obtain ⟨_, mls_u, hlt_af_u, hlt_u, _, hmls_u', hmls_u_eq, hloc_u⟩ := hframe.lookup_local hdecl_u
  rw [hmls_u] at hmls_u'
  injection hmls_u' with hmls_u'
  subst hmls_u'
  have hcache_u := hloc_u.layout_eq
  let layW := translateTy wDecl.ty body.layouts
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame w hlt_w layW
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 w none topFrame.localsIdentity, layW⟩
  have hevalPlace : annealEvalPlace body.localDecls body.layouts ⟨w, #[]⟩ m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_w hdecl_w (by rw [hmls_w_eq]; exact hcache_w)
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hmls_u₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp), c_u⟩ := by
    have h := Array.getElem?_eq_getElem hlt_u₀
    dsimp only [topFrame₀, cacheFrameLocalLayout] at h ⊢
    rw [Array.getElem?_set_ne _ hwu] at h
    rw [hmls_u] at h
    exact (Option.some.inj h).symm
  let topFrame₀' := cacheFrameLocalLayout topFrame₀ u hlt_u₀ layU
  have hlt_u₀' : u < topFrame₀'.locals.size := by
    dsimp only [topFrame₀']; rw [cacheFrameLocalLayout_size]; exact hlt_u₀
  let topFrame₁ := deinitFrameLocal topFrame₀' u hlt_u₀'
  let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
  have hop : annealEvalOperand body.localDecls body.layouts (.Move ⟨u, #[]⟩) (some layW) m₀ =
      .ok ⟨.indirect mp, layU⟩ m₁ :=
    annealEvalOperand_move_live (m := m₀) rfl hlt_u₀ hdecl_u hmls_u₀ hcache_u
  have hlt_w₁ : w < topFrame₁.locals.size := by
    dsimp only [topFrame₁, topFrame₀', topFrame₀, deinitFrameLocal]
    rw [Array.size_set, cacheFrameLocalLayout_size, cacheFrameLocalLayout_size]
    exact hlt_w
  have hmls_w₁ : topFrame₁.locals[w]? = some { mls_w with layout := some layW } := by
    dsimp only [topFrame₁, topFrame₀', topFrame₀, deinitFrameLocal, cacheFrameLocalLayout]
    simp [Ne.symm hwu, hmls_w_eq]
  have hw₁ : topFrame₁.locals[w]'hlt_w₁ = { mls_w with layout := some layW } := by
    have h := Array.getElem?_eq_getElem hlt_w₁
    rw [hmls_w₁] at h
    exact (Option.some.inj h).symm
  have hc_w₁ : (topFrame₁.locals[w]'hlt_w₁).layout = some layW := by rw [hw₁]
  have hval_w₁ : (topFrame₁.locals[w]'hlt_w₁).value = .live (.immediate .uninit) := by
    rw [hw₁]; exact hmls_w_val
  obtain ⟨alloc, htry, hbs, _, hnat, hmut, hal, hprov_alloc, hmask_alloc⟩ :=
    freshUnionAlloc_spec layW.layout.size layW.layout.align.abi (translateTy_align_pow2_le_29 _ _)
  have hraw_alloc := tryNew_uninit_raw layW.layout.size layW.layout.align.abi alloc htry
  cases hmem with
  | mk allocId tag baseAddr la msc hprov_u hmis_u hmeta_u hlive_u hbase_u hptr_u hovf_u hsz_u
      hlen_u hmut_u hp_u hal_u hex_u hnat_u hk hmask_u hrel hprim hf0imm hraw_u =>
  have hlayW_sz : layW.layout.size = translateSizeBytes S := hwt_w.size_eq
  have hlayW_toNat : layW.layout.size.bytes.toNat = S := by
    rw [hlayW_sz]
    exact translateSizeBytes_toNat_of_valid hS
  obtain ⟨A_w, hcopy_w, hA_sz, hA_len, hA_align, hA_mut, hA_prov, _, hA_mask_pred,
      hA_extra, hA_native, hA_raw⟩ :=
    union_copy_freshAlloc_spec (src := la.allocation)
      (dest := alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree))
      hS hrel.validBytes hk hlen_u hsz_u hp_u hmask_u
      (by show unionAllocRaw alloc = Array.replicate S 0; rw [hraw_alloc, hlayW_toNat])
      (by show alloc.byteSize = translateSizeBytes S; rw [hbs, hlayW_sz])
      hmut hprov_alloc
      (by show alloc.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes S) false
          rw [hmask_alloc, hlayW_sz])
  have hcopy_w' : Miri.Memory.Allocation.copy la.allocation
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO layW.layout.size)
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true (alloc.withExtra none) =
        .ok () A_w := by
    rw [hlayW_sz]
    exact hcopy_w
  have hmemcopy := annealMemCopyOp_freshUnion (body := body) (m := m₁) rfl hlt_w₁ hdecl_w hc_w₁
    hval_w₁ hwt_w.sized htry hres hnodup hprov_u hlive_u hbase_u hptr_u hcopy_w'
    layU topFrame.localsIdentity
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨w, #[]⟩
      (translateRvalue (.use (.move ⟨u, .nil⟩))) = true := by
    have hunion := isUnionLocal_of_wellTyped hdecl_w hwt_w
    simp [lm24Assign, lm24Place, hunion]
  have huse : usesMemCopy ⟨.indirect mp, layU⟩ = true := by
    simp [usesMemCopy, layU, hfields_u]
  have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
      ⟨w, #[]⟩ true m = .ok destPlace m₀ := hevalPlace
  have hop' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.move ⟨u, .nil⟩))
      (some ((annealRvalueHooksLM2_4 body.localDecls body.layouts).placeLayout destPlace)) m₀ =
      .ok ⟨.indirect mp, layU⟩ m₁ := hop
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (.move ⟨u, .nil⟩)), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp, layU⟩ destPlace) m₁ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace']
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop']
    simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2, huse, ↓reduceIte]
  let mp_w := stackAllocPlace id
  let mach₃ := stackAllocMachine m.machine mem' id A_w
  let tf₃ := setFrameLocalIndirect topFrame₁ w hlt_w₁ mp_w
  let st₃ : AnnealStepState := { stack := ⟨#[tf₃]⟩, machine := mach₃ }
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (.move ⟨u, .nil⟩)), span⟩) m = (st₃, .ok ()) := by
    rw [hm_eval]
    unfold Miri.Interpreter.runRvalue
    rw [hmemcopy]
  have hloc₃ : tf₃.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hframe.location_eq
  have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
    hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl hloc₃
  let locals₁ := s.frame.locals.set u .uninit
  have hvld := validateLoadedValue_unionWhole_true hdecl_u hwt true
    (.aggregate 0 (unionSlotFields n f (.scalar sc)))
  simp only [↓reduceIte] at hvld
  have hrv : evalRvalue s.frame.locals (.use (.move ⟨u, .nil⟩)) s.memory body.localDecls
      body.layouts =
      .ok (.aggregate 0 (unionSlotFields n f (.scalar sc))) locals₁ s.memory := by
    unfold evalRvalue; dsimp only; rw [hbor, hcaller]
    simp only [evalOperand, hu_slot, set?_eq_some_set hlt_af_u, hvld, locals₁]
  have hw_uninit₁ : get? locals₁ w = some .uninit := by
    dsimp only [locals₁]
    rw [get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hwu), ← get?_eq_getElem?]
    exact hw_uninit
  have hlt_af_w₁ : w < locals₁.length := by
    dsimp only [locals₁]; rw [List.length_set]; exact hlt_af_w
  let locals₂ := locals₁.set w (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))
  have ha_ok : evalStmt s ⟨.assign ⟨w, .nil⟩ (.use (.move ⟨u, .nil⟩)), span⟩
      body.localDecls body.layouts = MirStepNode.step (advanceStmt s locals₂ s.memory) := by
    unfold evalStmt
    dsimp only
    rw [hrv]
    simp only []
    rw [hprot, hbor]
    dsimp only [invalidateConflictingBorrows]
    rw [hmem_same]
    simp [hw_uninit₁, set?_eq_some_set hlt_af_w₁, locals₂]
  obtain ⟨hlive_b, hfreshne, hbase_b⟩ := stackAllocMachine_live_base (mach := m.machine) A_w hres
  have hmem_w : UnionMemRel mach₃ wDecl.ty body.layouts S f0Ty sc mp_w :=
    .mk id .one (annealStackBaseAddr id) ⟨.stack, A_w⟩ msc rfl rfl rfl
      (by simp [mach₃, stackAllocMachine])
      (lookupBaseAddr_stackAllocMachine_self _ _ _ _) rfl (annealStackBaseAddr_add_lt id hS16)
      hA_sz hA_len hA_mut hA_prov
      (by rw [hA_align]; exact hal) hA_extra (by rw [hA_native]; exact hnat) hk hA_mask_pred hrel
      hprim hf0imm (by rw [hA_raw]; exact hraw_u)
  have hframe₀' : FrameRelLM2_4 body m.machine s.frame topFrame₀' :=
    (hframe.cache_local_layout hdecl_w hlt_w).cache_local_layout hdecl_u hlt_u₀
  have hnew_u : UnionLocalRel m.machine uDecl body.layouts .uninit
      { topFrame₀'.locals[u]'hlt_u₀' with value := .live (.immediate .uninit) } := by
    have hlay_u : (topFrame₀'.locals[u]'hlt_u₀').layout = some layU := by
      simp [topFrame₀', cacheFrameLocalLayout]
    exact .base .uninit _ (.immediate .uninit .uninit _
      (by rw [hlay_u]; intro l hl; exact (Option.some.inj hl).symm) (Or.inl ⟨rfl, rfl⟩))
  have hframe₁ : FrameRelLM2_4 body m.machine { s.frame with locals := locals₁ } topFrame₁ :=
    hframe₀'.update_local hdecl_u .uninit (.live (.immediate .uninit)) hnew_u
  have hdisj₀' : MemoryAllocDisjoint topFrame₀' :=
    (hdisj.cache_layout hlt_w _).cache_layout hlt_u₀ _
  have hdisj₁ : MemoryAllocDisjoint topFrame₁ := by
    intro i j mp_i mp_j lay_i lay_j hij hi hj
    dsimp only [topFrame₁, deinitFrameLocal] at hi hj
    rw [Array.getElem?_set] at hi hj
    by_cases hi_u : u = i
    · subst hi_u; simp at hi
    · simp only [hi_u, ↓reduceIte] at hi
      by_cases hj_u : u = j
      · subst hj_u; simp at hj
      · simp only [hj_u, ↓reduceIte] at hj
        exact hdisj₀' i j mp_i mp_j lay_i lay_j hij hi hj
  let tf_fin := { tf₃ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
  let m' : AnnealStepState := { st₃ with stack := ⟨#[tf_fin]⟩ }
  have hframe_fin : FrameRelLM2_4 body mach₃ (advanceStmt s locals₂ s.memory).frame tf_fin :=
    { body_eq := hframe.body_eq
      location_eq := rfl
      af_locals_len := by
        show (locals₁.set w _).length = _
        rw [List.length_set, List.length_set]
        exact hframe.af_locals_len
      mf_locals_size := by
        show (topFrame₁.locals.set w _ hlt_w₁).size = _
        rw [Array.size_set]
        exact hframe₁.mf_locals_size
      locals_rel := by
        intro i decl slot mls hdecl hslot hmls
        have hslot' : get? locals₂ i = some slot := hslot
        have hmls' : (topFrame₁.locals.set w
            { topFrame₁.locals[w]'hlt_w₁ with value := .live (.indirect mp_w) } hlt_w₁)[i]? =
            some mls := hmls
        rw [get?_eq_getElem?, List.getElem?_set] at hslot'
        rw [Array.getElem?_set] at hmls'
        by_cases hiw : w = i
        · subst hiw
          simp only [↓reduceIte, hlt_af_w₁, Option.some.injEq] at hslot' hmls'
          subst hslot' hmls'
          rw [hdecl_w] at hdecl
          cases hdecl
          refine .union S n f f0Ty sc mp_w _ ?_ hwt_w hfields_w hf hmem_w
          intro l hl
          rw [hc_w₁] at hl
          exact (Option.some.inj hl).symm
        · simp only [hiw, ↓reduceIte] at hslot' hmls'
          exact (hframe₁.locals_rel i decl slot mls hdecl hslot' hmls').of_live_base hlive_b
            hbase_b }
  have hdisj_fin : MemoryAllocDisjoint tf_fin := by
    intro i j mp_i mp_j lay_i lay_j hij hi hj
    dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hi hj
    rw [Array.getElem?_set] at hi hj
    by_cases hi_w : w = i
    · subst hi_w
      have hj_w : w ≠ j := hij
      simp only [hj_w, ↓reduceIte] at hj
      simp only [↓reduceIte] at hi
      obtain ⟨a, la', ha, hla⟩ := hframe₁.indirect_allocId hj
      injection hi with hi
      injection hi with hv _
      injection hv with hv
      injection hv with hv
      subst hv
      rw [ha]
      simp only [mp_w, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
        Option.some.injEq]
      exact fun h => hfreshne a la' hla h.symm
    · simp only [hi_w, ↓reduceIte] at hi
      by_cases hj_w : w = j
      · subst hj_w
        simp only [↓reduceIte] at hj
        obtain ⟨a, la', ha, hla⟩ := hframe₁.indirect_allocId hi
        injection hj with hj
        injection hj with hv _
        injection hv with hv
        injection hv with hv
        subst hv
        rw [ha]
        simp only [mp_w, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
          Option.some.injEq]
        exact hfreshne a la' hla
      · simp only [hj_w, ↓reduceIte] at hj
        exact hdisj₁ i j mp_i mp_j lay_i lay_j hij hi hj
  have hstate' : StateRelLM2_4 body (advanceStmt s locals₂ s.memory) m' :=
    StateRelLM2_4.mk tf_fin rfl hretCont ⟨retLay, hretPlace⟩ hframe_fin hcal hstack hbor hprot
      hcaller hdisj_fin
  have hu_imm_fin : IsImmediateFrameLocal tf_fin u := by
    intro mls hmls mp' hmp'
    dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hmls
    rw [Array.getElem?_set_ne _ hwu] at hmls
    dsimp only [topFrame₁, deinitFrameLocal] at hmls
    rw [Array.getElem?_set_self] at hmls
    injection hmls with hmls
    rw [← hmls] at hmp'
    cases hmp'
  have himm_fin : ∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ w →
      IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf_fin j := by
    intro tf htf j hj himm_j
    rw [hframes] at htf
    have htf' : topFrame = tf := by simpa using htf
    subst htf'
    by_cases hju : j = u
    · subst hju; exact hu_imm_fin
    · have h₀' := (himm_j.cache_layout hlt_w layW).cache_layout hlt_u₀ layU
      intro mls hmls
      dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hmls
      rw [Array.getElem?_set_ne _ (Ne.symm hj)] at hmls
      dsimp only [topFrame₁, deinitFrameLocal] at hmls
      rw [Array.getElem?_set_ne _ (Ne.symm hju)] at hmls
      exact h₀' mls hmls
  refine ⟨advanceStmt s locals₂ s.memory, m', mp_w, tf_fin, by rw [hstep_a, ha_ok],
    hstep_m, hstate', ?_, ?_, ?_, rfl, ⟨(topFrame₁.locals[w]'hlt_w₁).layout, ?_⟩,
    ⟨some layU, ?_⟩, hmem_w, LiveAllocsNodup.stackAllocMachine A_w hnodup hres,
    hu_imm_fin, himm_fin, rfl, rfl,
    fun _ hw hb => MemoryHighWater.stackAllocMachine A_w hw hb hres⟩
  · simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_w₁]
  · dsimp only [advanceStmt, locals₂, locals₁]
    rw [get?_eq_getElem?, List.getElem?_set_ne hwu]
    simp [hlt_af_u]
  · intro j hjw hju
    simp [advanceStmt, locals₂, locals₁, get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hjw),
      List.getElem?_set_ne (Ne.symm hju)]
  · simp [tf_fin, tf₃, setFrameLocalIndirect]
  · dsimp only [tf_fin, tf₃, setFrameLocalIndirect]
    rw [Array.getElem?_set_ne _ hwu]
    dsimp only [topFrame₁, deinitFrameLocal]
    rw [Array.getElem?_set_self]
    have hlay_u : (topFrame₀'.locals[u]'hlt_u₀').layout = some layU := by
      simp [topFrame₀', cacheFrameLocalLayout]
    rw [hlay_u]

/-! ## 8. Headline Union Theorems -/

/-- **`union_uninit_bytes_read_ub_simulation`** (`LM-2.4`): reading a sibling
field `j ≠ f` of `w` bytes from a union that holds field `f`'s value of
`k = sc.sizeBytes < w ≤ S` bytes is undefined behavior in both machines. -/
theorem union_uninit_bytes_read_ub_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {r u j : Local} {fty : Ty} {isMove : Bool} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩)
    {rDecl uDecl : LocalDecl}
    (hdecl_r : get? body.localDecls r = some rDecl) (hr_ty : rDecl.ty = fty)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hprim : IsPrimScalarTy fty) {w : Nat} (hw : ValidScalarBytes w)
    (hsz : (translateTy fty body.layouts).layout.size = translateSizeBytes w)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n) (hj : j < n)
    {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hr_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame r)
    (hjne : j ≠ f) (hkw : sc.sizeBytes < w) (hwS : w ≤ S)
    (hfl : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size := by exact ⟨_, rfl, rfl⟩) :
    stepMirFn body s = .fail .ub ∧
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) :=
  (step_union_field_read_simulation hstate hnodup hphase hbb hstmt hdecl_r hr_ty hdecl_u hprim
    hw hsz hwt hfields hf hj hu_slot hu_mls hmem hr_imm hfl).2 hjne hkw hwS

/-- **`union_field_write_read_same_field_simulation`** (`LM-2.4` + `D13a` general
active field `f < n`): writing field `f` of an uninitialized union with the union
aggregate `_u = U { field_f: op }` and then reading the same field back with
`_r = copy _u.f` (or `move _u.f`) runs in lockstep in both machines, and on normal
steps `_r` ends up holding the value `sc` of `op`, although `lean-miri`'s union
keeps its bytes past field `f` uninitialized throughout. -/
theorem union_field_write_read_same_field_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {u r : Local} {d : DefPath} {f : Nat} {op : MirAst.Operand}
    {isMove : Bool} {span₁ span₂ : String} {f0Ty : Ty}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt₁ : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span₁⟩)
    (hstmt₂ : get? bb.statements (s.frame.stmtIdx + 1) =
      some ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u f f0Ty)), span₂⟩)
    {uDecl rDecl : LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    (hdecl_r : get? body.localDecls r = some rDecl) (hr_ty : rDecl.ty = f0Ty)
    {S n : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl)
    (hfl_sized : fl.layout.isSized = true)
    (hu_uninit : get? s.frame.locals u = some .uninit)
    (hu_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame u)
    (hr_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame r)
    (hprim0 : IsPrimScalarTy f0Ty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op f0Ty)
    (hf0_le : (translateTy f0Ty body.layouts).layout.size.bytes.toNat ≤ S)
    (hadt : ∃ args, uDecl.ty.kind = .adt d args := by exact ⟨_, rfl⟩)
    (hfl_sz : fl.layout.size = (translateTy f0Ty body.layouts).layout.size := by rfl)
    (hdecls_adt : ∀ l ∈ collectAdtLayoutsInDecls body.layouts d body.localDecls,
      body.layouts.lookup uDecl.ty.layoutIdx = some l := by
        simp [collectAdtLayoutsInDecls, collectAdtLayoutsInTyAux, stringEq,
          LayoutTable.lookup, get?]) :
    StepRelLM2_4 body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    ∀ s₁, stepMirFn body s = .step s₁ →
      ∃ (m₁ : AnnealStepState) (sc : MirAst.ScalarInt),
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m₁, .ok true) ∧
        evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
          .ok (.scalar sc) s.frame.locals ∧
        StepRelLM2_4 body m₁ (stepMirFn body s₁)
          (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m₁) ∧
        ∀ s₂, stepMirFn body s₁ = .step s₂ →
          get? s₂.frame.locals r = some (.init (.scalar sc)) := by
  have hstate₀ := hstate
  rcases hstate₀ with ⟨tf₀, hframes₀, _, _, _, _, _, _, _, _, _⟩
  obtain ⟨hrel₁, hpost₁⟩ := step_union_aggregate_simulation hstate hnodup hcanRes hphase hbb hstmt₁
    hdecl_u hwt hfields hf hfl hfl_sized hu_uninit hu_imm hprim0 hop hf0_le hadt hfl_sz hdecls_adt
  refine ⟨hrel₁, fun s₁ hs₁ => ?_⟩
  obtain ⟨sc, mp, m₁, tf₁, hstep₁, hop_val, hstate₁, hu_slot₁, hframes₁, ⟨c, hmls_u₁⟩, hmem₁,
    hnodup₁, himm₁, _, hblk₁, hidx₁, _⟩ := hpost₁ s₁ hs₁
  have hru : r ≠ u := primScalar_ne_union_local hdecl_u hwt hdecl_r (hr_ty ▸ hprim0)
  obtain ⟨hf0sz, hkv⟩ := hmem₁.f0_size
  have hbb₁ : get? body.basicBlocks s₁.frame.blockIdx = some bb := by rw [hblk₁]; exact hbb
  have hstmt₂' : get? bb.statements s₁.frame.stmtIdx =
      some ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u f f0Ty)), span₂⟩ := by
    rw [hidx₁]; exact hstmt₂
  have hu_mls₁ : ∀ topFrame, m₁.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩ := by
    intro tf htf
    rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h
    exact ⟨c, hmls_u₁⟩
  have hr_imm₁ : ∀ topFrame, m₁.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame r := by
    intro tf htf
    rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h
    exact himm₁ tf₀ hframes₀ r hru (hr_imm tf₀ hframes₀)
  have hread := step_union_field_read_simulation hstate₁ hnodup₁ hphase hbb₁ hstmt₂' hdecl_r hr_ty
    hdecl_u hprim0 hkv hf0sz hwt hfields hf hf hu_slot₁ hu_mls₁ hmem₁ hr_imm₁ ⟨fl, hfl, hfl_sz⟩
  obtain ⟨hrel₂, hval₂, _⟩ := hread.1 rfl rfl
  exact ⟨m₁, sc, hstep₁, hop_val, hrel₂, hval₂⟩

/-! ## 9. `Subslice` Projections (`evalProjection_subslice_simulation`) -/

theorem dropValues_eq_drop : ∀ (n : Nat) (xs : List Value), dropValues n xs = xs.drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: xs => dropValues_eq_drop n xs

theorem takeValues_eq_take : ∀ (n : Nat) (xs : List Value), takeValues n xs = xs.take n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, x :: xs => by
    show x :: takeValues n xs = x :: xs.take n
    rw [takeValues_eq_take n xs]

/-- The end index of the subslice `fromIdx..toIdx` (`fromEnd`) of a
`count`-element array: `toIdx`, or `count - toIdx` when `toIdx` counts from the
end. -/
def subsliceEnd (count toIdx : Nat) (fromEnd : Bool) : Nat :=
  if fromEnd then count - toIdx else toIdx

/-- The subslice bounds that rustc's MIR validation guarantees for an array of
`count` elements: `fromIdx ≤ toIdx ≤ count`, or `fromIdx + toIdx ≤ count` when
`toIdx` counts from the end. -/
def SubsliceInBounds (count fromIdx toIdx : Nat) (fromEnd : Bool) : Prop :=
  (fromEnd = false ∧ fromIdx ≤ toIdx ∧ toIdx ≤ count) ∨
    (fromEnd = true ∧ fromIdx + toIdx ≤ count)

/-- Anneal's `extractSubslice` on in-bounds indices takes the elements
`[fromIdx, subsliceEnd)`. -/
theorem extractSubslice_inBounds {elems : List Value} {count fromIdx toIdx : Nat}
    {fromEnd : Bool} (hlen : elems.length = count)
    (hin : SubsliceInBounds count fromIdx toIdx fromEnd) :
    extractSubslice elems fromIdx toIdx fromEnd =
      some ((elems.drop fromIdx).take (subsliceEnd count toIdx fromEnd - fromIdx)) := by
  unfold extractSubslice subsliceEnd
  have hlen' : length elems = count := hlen
  simp only [hlen']
  rcases hin with ⟨rfl, h1, h2⟩ | ⟨rfl, h1⟩
  · have hb1 : Nat.ble toIdx count = true := Nat.ble_eq.mpr h2
    have hb2 : Nat.ble fromIdx toIdx = true := Nat.ble_eq.mpr h1
    simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte, takeValues_eq_take, dropValues_eq_drop,
      Nat.sub_eq]
  · have hb1 : Nat.ble toIdx count = true := Nat.ble_eq.mpr (by omega)
    have hb2 : Nat.ble fromIdx (count - toIdx) = true := Nat.ble_eq.mpr (by omega)
    simp only [hb1, Nat.sub_eq, hb2, ↓reduceIte, takeValues_eq_take, dropValues_eq_drop]

private theorem list_take_set_drop_eq_set {α : Type} :
    ∀ (xs : List α) (fromIdx endIdx off : Nat) (v : α),
      fromIdx ≤ endIdx →
      endIdx ≤ xs.length →
      off < endIdx - fromIdx →
      xs.take fromIdx ++ (((xs.drop fromIdx).take (endIdx - fromIdx)).set off v ++ xs.drop endIdx) =
        xs.set (fromIdx + off) v := by
  intro xs fromIdx endIdx off v hfe hel hoff
  apply List.ext_getElem
  · simp [Nat.min_eq_left (Nat.le_trans hfe hel), Nat.min_eq_left (by omega : endIdx - fromIdx ≤ xs.length - fromIdx)]
    omega
  · intro i hi1 hi2
    have hlen_pre : (xs.take fromIdx).length = fromIdx := by simp; omega
    have hlen_mid : (((xs.drop fromIdx).take (endIdx - fromIdx)).set off v).length = endIdx - fromIdx := by
      simp; omega
    by_cases hlt1 : i < fromIdx
    · rw [List.getElem_append_left (by rw [hlen_pre]; exact hlt1), List.getElem_take,
        List.getElem_set_ne (by omega)]
    · rw [List.getElem_append_right (by rw [hlen_pre]; omega)]
      simp only [hlen_pre]
      by_cases hlt2 : i < endIdx
      · rw [List.getElem_append_left (by rw [hlen_mid]; omega)]
        by_cases heq : i - fromIdx = off
        · have hi_eq : i = fromIdx + off := by omega
          subst hi_eq
          simp [Nat.add_sub_cancel_left, List.getElem_set_self]
        · rw [List.getElem_set_ne (Ne.symm heq), List.getElem_take, List.getElem_drop,
            List.getElem_set_ne (by omega)]
          congr 1; omega
      · rw [List.getElem_append_right (by rw [hlen_mid]; omega), List.getElem_drop,
          List.getElem_set_ne (by omega)]
        congr 1; omega

theorem writeProjectedForLocal_subslice_constIndex
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (arrIdx : Local) (elems : List Value) {count fromIdx toIdx off minLen : Nat}
    {fromEnd : Bool} (v : Value)
    (hlen : elems.length = count)
    (hin : SubsliceInBounds count fromIdx toIdx fromEnd)
    (hoff_lt : off < minLen)
    (hmin_le : minLen ≤ subsliceEnd count toIdx fromEnd - fromIdx) :
    writeProjectedForLocal locals localDecls layouts arrIdx
        (ensureNestedFieldShells (.aggregate 0 elems)
          [.subslice fromIdx toIdx fromEnd, .constantIndex off minLen false])
        [.subslice fromIdx toIdx fromEnd, .constantIndex off minLen false] v =
      .ok (.aggregate 0 (elems.set (fromIdx + off) v)) := by
  dsimp only [ensureNestedFieldShells]
  unfold writeProjectedForLocal
  rw [placeTouchesUnion_subslice_constIndex]
  dsimp only
  simp only [writeProjectedValue]
  have hlen_tr : length elems = count := hlen
  rcases hin with ⟨rfl, h1, h2⟩ | ⟨rfl, h1⟩
  · simp only [subsliceEnd, Bool.false_eq_true, ↓reduceIte] at hmin_le
    have hoff_cnt : off < toIdx - fromIdx := Nat.lt_of_lt_of_le hoff_lt hmin_le
    have hext : extractSubslice elems fromIdx toIdx false =
        some ((elems.drop fromIdx).take (toIdx - fromIdx)) := by
      unfold extractSubslice
      rw [hlen_tr]; dsimp only
      rw [Nat.ble_eq.mpr h2]; dsimp only
      rw [Nat.ble_eq.mpr h1]; dsimp only
      rw [dropValues_eq_drop, takeValues_eq_take]; rfl
    rw [hext]; dsimp only
    have hsub_len : ((elems.drop fromIdx).take (toIdx - fromIdx)).length = toIdx - fromIdx := by
      simp [hlen]; omega
    have hsub_len_tr : length ((elems.drop fromIdx).take (toIdx - fromIdx)) = toIdx - fromIdx :=
      hsub_len
    rw [hsub_len_tr, Nat.ble_eq.mpr hmin_le]; dsimp only
    rw [get?_eq_getElem?, List.getElem?_eq_getElem (by rw [hsub_len]; exact hoff_cnt)]; dsimp only
    rw [set?_eq_some_set (by rw [hsub_len]; exact hoff_cnt) v]; simp only []
    unfold replaceSubslice
    have hupd_len : length (((elems.drop fromIdx).take (toIdx - fromIdx)).set off v) =
        toIdx - fromIdx := by
      show (((elems.drop fromIdx).take (toIdx - fromIdx)).set off v).length = toIdx - fromIdx
      rw [List.length_set, hsub_len]
    rw [hlen_tr]; dsimp only
    rw [Nat.ble_eq.mpr h2]; dsimp only
    rw [Nat.ble_eq.mpr h1]; dsimp only
    rw [show Nat.sub toIdx fromIdx = toIdx - fromIdx from rfl, hupd_len, Nat.beq_refl]; dsimp only
    rw [takeValues_eq_take, dropValues_eq_drop,
      appendValueList_eq_append, appendValueList_eq_append,
      list_take_set_drop_eq_set elems fromIdx toIdx off v h1 (by omega) hoff_cnt]
  · simp only [subsliceEnd, ↓reduceIte] at hmin_le
    have h2 : toIdx ≤ count := by omega
    have hble1 : fromIdx ≤ count - toIdx := by omega
    have hoff_cnt : off < count - toIdx - fromIdx := Nat.lt_of_lt_of_le hoff_lt hmin_le
    have hext : extractSubslice elems fromIdx toIdx true =
        some ((elems.drop fromIdx).take (count - toIdx - fromIdx)) := by
      unfold extractSubslice
      rw [hlen_tr]; dsimp only
      rw [Nat.ble_eq.mpr h2]; dsimp only
      rw [show Nat.sub count toIdx = count - toIdx from rfl]
      rw [Nat.ble_eq.mpr hble1]; dsimp only
      rw [dropValues_eq_drop, takeValues_eq_take]; rfl
    rw [hext]; dsimp only
    have hsub_len : ((elems.drop fromIdx).take (count - toIdx - fromIdx)).length =
        count - toIdx - fromIdx := by
      simp [hlen]; omega
    have hsub_len_tr : length ((elems.drop fromIdx).take (count - toIdx - fromIdx)) =
        count - toIdx - fromIdx := hsub_len
    rw [hsub_len_tr, Nat.ble_eq.mpr hmin_le]; dsimp only
    rw [get?_eq_getElem?, List.getElem?_eq_getElem (by rw [hsub_len]; exact hoff_cnt)]; dsimp only
    rw [set?_eq_some_set (by rw [hsub_len]; exact hoff_cnt) v]; simp only []
    unfold replaceSubslice
    have hupd_len : length (((elems.drop fromIdx).take (count - toIdx - fromIdx)).set off v) =
        count - toIdx - fromIdx := by
      show (((elems.drop fromIdx).take (count - toIdx - fromIdx)).set off v).length =
        count - toIdx - fromIdx
      rw [List.length_set, hsub_len]
    rw [hlen_tr]; dsimp only
    rw [Nat.ble_eq.mpr h2]; dsimp only
    rw [show Nat.sub count toIdx = count - toIdx from rfl]
    rw [Nat.ble_eq.mpr hble1]; dsimp only
    rw [show Nat.sub (count - toIdx) fromIdx = count - toIdx - fromIdx from rfl, hupd_len,
      Nat.beq_refl]; dsimp only
    rw [takeValues_eq_take, dropValues_eq_drop,
      appendValueList_eq_append, appendValueList_eq_append,
      list_take_set_drop_eq_set elems fromIdx (count - toIdx) off v hble1 (by omega) hoff_cnt]

/-- Anneal's `extractSubslice` rejects a subslice counted from the end that
starts past the end it designates. -/
theorem extractSubslice_fromEnd_oob {elems : List Value} {count fromIdx toIdx : Nat}
    (hlen : elems.length = count) (hoob : count < fromIdx + toIdx) :
    extractSubslice elems fromIdx toIdx true = none := by
  unfold extractSubslice
  have hlen' : length elems = count := hlen
  simp only [hlen']
  by_cases ht : toIdx ≤ count
  · have hb1 : Nat.ble toIdx count = true := Nat.ble_eq.mpr ht
    have hb2 : Nat.ble fromIdx (count - toIdx) = false := by
      cases h : Nat.ble fromIdx (count - toIdx) with
      | false => rfl
      | true => exact absurd (Nat.le_of_ble_eq_true h) (by omega)
    simp only [hb1, Nat.sub_eq, hb2]
  · have hb1 : Nat.ble toIdx count = false := by
      cases h : Nat.ble toIdx count with
      | false => rfl
      | true => exact absurd (Nat.le_of_ble_eq_true h) ht
    simp only [hb1]

/-- Anneal's `extractSubslice` rejects inverted bounds `toIdx < fromIdx`. -/
theorem extractSubslice_inverted {elems : List Value} {fromIdx toIdx : Nat}
    (hinv : toIdx < fromIdx) :
    extractSubslice elems fromIdx toIdx false = none := by
  have hb2 : Nat.ble fromIdx toIdx = false := by
    cases h : Nat.ble fromIdx toIdx with
    | false => rfl
    | true => exact absurd (Nat.le_of_ble_eq_true h) (by omega)
  unfold extractSubslice
  simp only [hb2]
  cases Nat.ble toIdx (length elems) <;> rfl

/-- A contiguous run `[f, f + cnt)` of an `ArraySliceRel` array is an
`ArraySliceRel` array of `cnt` elements starting `f` elements later. -/
theorem ArraySliceRel.subslice {elemKind : RigidTy} {count : Nat} {layouts : LayoutTable}
    {elems : List Value} {relOffset : Miri.ABI.Size}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (h : ArraySliceRel elemKind count layouts elems relOffset alloc)
    {f cnt : Nat} (hfc : f + cnt ≤ count) :
    ArraySliceRel elemKind cnt layouts ((elems.drop f).take cnt)
      (Miri.ABI.Size.ofBytes (relOffset.bytes + UInt64.ofNat
        (f * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)))
      alloc := by
  let es := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat
  have hbound := h.slice_in_bounds
  have hbs : alloc.byteSize.bytes.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have hmul1 : (f + cnt) * es ≤ count * es := Nat.mul_le_mul_right _ hfc
  have hadd : (f + cnt) * es = f * es + cnt * es := Nat.add_mul _ _ _
  have hfes : relOffset.bytes.toNat + f * es < 2 ^ 64 := by
    dsimp only [es] at *
    omega
  have hoff : (Miri.ABI.Size.ofBytes (relOffset.bytes + UInt64.ofNat (f * es))).bytes.toNat =
      relOffset.bytes.toNat + f * es := by
    simp only [Miri.ABI.Size.ofBytes]
    rw [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (a := f * es) (by omega)]
    exact Nat.mod_eq_of_lt hfes
  refine
    { elems_len := ?_
      alloc_len := h.alloc_len
      alloc_mut := h.alloc_mut
      alloc_prov := h.alloc_prov
      alloc_mask := h.alloc_mask
      slice_in_bounds := ?_
      elem_rel := ?_ }
  · rw [List.length_take, List.length_drop, h.elems_len]
    omega
  · show (Miri.ABI.Size.ofBytes (relOffset.bytes + UInt64.ofNat (f * es))).bytes.toNat + cnt * es ≤ _
    rw [hoff]
    dsimp only [es] at *
    omega
  · intro k elemVal hk
    rw [get?_eq_getElem?, List.getElem?_take] at hk
    split at hk
    · rw [List.getElem?_drop] at hk
      obtain ⟨sc, msc, hv, hsz, hbool, hchar, hrel, hread⟩ :=
        h.elem_rel (f + k) elemVal (by rw [get?_eq_getElem?]; exact hk)
      refine ⟨sc, msc, hv, hsz, hbool, hchar, hrel, ?_⟩
      have hoffk : Miri.ABI.Size.ofBytes
          ((Miri.ABI.Size.ofBytes (relOffset.bytes + UInt64.ofNat (f * es))).bytes +
            UInt64.ofNat (k * es)) =
          Miri.ABI.Size.ofBytes (relOffset.bytes + UInt64.ofNat ((f + k) * es)) := by
        simp only [Miri.ABI.Size.ofBytes, Nat.add_mul, UInt64.ofNat_add, UInt64.add_assoc]
      dsimp only [es] at hoffk
      rw [hoffk]
      exact hread
    · cases hk

/-- `Size.mul` of an array element size by an element count within the array
does not overflow. -/
theorem elemSize_mul_ok {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count) {i : Nat} (hi : i ≤ count) :
    (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.mul (UInt64.ofNat i) =
      .ok (Miri.ABI.Size.ofBytes
        ((translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes *
          UInt64.ofNat i)) := by
  let elemSize := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
  have hcnt32 := hwf.count_lt_two_pow_32
  have hi_toNat : (UInt64.ofNat i).toNat = i := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : i < 2 ^ 64))]
  have hmul_lt64 : elemSize.bytes.toNat * (UInt64.ofNat i).toNat < 2 ^ 64 := by
    rw [hi_toNat, Nat.mul_comm]
    have hle : i * elemSize.bytes.toNat ≤ count * elemSize.bytes.toNat := Nat.mul_le_mul_right _ hi
    have htot := hwf.total_bytes_bound
    dsimp only [elemSize] at hle ⊢
    omega
  unfold Miri.ABI.Size.mul
  dsimp only
  have hcond :
      (UInt64.ofNat i != 0 &&
        elemSize.bytes * UInt64.ofNat i / UInt64.ofNat i != elemSize.bytes) = false := by
    by_cases hz : UInt64.ofNat i = 0
    · simp [hz]
    · have hpos : 0 < (UInt64.ofNat i).toNat := by
        exact Nat.pos_of_ne_zero (fun h0 => hz (UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h0)))
      have hprod_toNat :
          (elemSize.bytes * UInt64.ofNat i).toNat = elemSize.bytes.toNat * (UInt64.ofNat i).toNat := by
        rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by simpa [UInt64.size] using hmul_lt64)]
      have hdiv : elemSize.bytes * UInt64.ofNat i / UInt64.ofNat i = elemSize.bytes := by
        apply UInt64.eq_of_toBitVec_eq
        apply BitVec.eq_of_toNat_eq
        change ((elemSize.bytes * UInt64.ofNat i) / UInt64.ofNat i).toNat = elemSize.bytes.toNat
        rw [UInt64.toNat_div, hprod_toNat, Nat.mul_div_left _ hpos]
      simp [hdiv]
  rw [hcond]
  rfl

/-- **`evalProjection_subslice_simulation`** (`LM-2.4`): the `Subslice`
projection `a[fromIdx..toIdx]` (or `a[fromIdx..len - toIdx]` when `fromEnd`) of
a memory-backed array `a` of `count` primitive scalars related by `MemPlaceRel`,
evaluated by Anneal's `readProjectedValue` and by the vendored
`Miri.Interpreter.projectSubslice` (with `annealSubsliceProjectionCx`, whose
sub-array layout is `annealSubsliceLayout`).

1. In bounds (`SubsliceInBounds`): Anneal's value is the sub-array of elements
   `[fromIdx, end)`, and `lean-miri`'s place is the same allocation at
   `fromIdx * elemSize` bytes further, with layout `[T; end - fromIdx]`; its
   bytes hold those elements (`ArraySliceRel` at the new offset).
2. A subslice counted from the end with `count < fromIdx + toIdx` is undefined
   behavior in both machines (a failed bounds check in `lean-miri`). -/
theorem evalProjection_subslice_simulation
    {mach : AnnealMachine}
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (locals : List LocalSlot)
    {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {elems : List Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup mach)
    (hmp : MemPlaceRel mach arrTy layouts (some (.aggregate 0 elems)) mp)
    (fromIdx toIdx : Nat) (fromEnd : Bool) :
    let cx := annealSubsliceProjectionCx frame layouts mach
    let arrLay := translateTy arrTy layouts
    let es := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
    let cnt := subsliceEnd count toIdx fromEnd - fromIdx
    let sub := (elems.drop fromIdx).take cnt
    (SubsliceInBounds count fromIdx toIdx fromEnd →
      readProjectedValue locals (.aggregate 0 elems) [.subslice fromIdx toIdx fromEnd] =
        .ok (.aggregate 0 sub) ∧
      annealProjectList cx ⟨.indirect mp, arrLay⟩ [.Subslice fromIdx toIdx fromEnd] =
        .ok ⟨.indirect { mp with
                ptr := { mp.ptr with
                  offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + es.bytes * UInt64.ofNat fromIdx) },
                metadata := .none },
             { ty := arrLay.ty,
               layout := { arrLay.layout with
                 fields := .Array es (UInt64.ofNat cnt),
                 size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt) } }⟩ ∧
      ∃ (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (baseAddr : UInt64)
        (relOffset : Miri.ABI.Size)
        (localAlloc : Miri.Memory.LocalAllocation AnnealProv
          (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind),
        mp.ptr.provenance = some (.concrete allocId tag) ∧
        (allocId, localAlloc) ∈ mach.memory.live.toList ∧
        mach.lookupBaseAddr allocId = some baseAddr ∧
        mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes) ∧
        ArraySliceRel elemKind cnt layouts sub
          (Miri.ABI.Size.ofBytes (relOffset.bytes + UInt64.ofNat (fromIdx * es.bytes.toNat)))
          localAlloc.allocation) ∧
    (fromEnd = true → count < fromIdx + toIdx → fromIdx + toIdx < 2 ^ 64 →
      readProjectedValue locals (.aggregate 0 elems) [.subslice fromIdx toIdx fromEnd] = .ub ∧
      ∃ msg, (annealProjectList cx ⟨.indirect mp, arrLay⟩
        [.Subslice fromIdx toIdx fromEnd]).mapError annealLiftProjectionError =
          .error (.undefinedBehavior msg)) := by
  intro cx arrLay es cnt sub
  let base : Miri.Interpreter.OpTy AnnealProv := ⟨.indirect mp, arrLay⟩
  have hfields : base.layout.layout.fields = .Array es (UInt64.ofNat count) := hwf.arr_fields
  have hisSized : base.layout.layout.isSized = true := hwf.arr_isSized
  have hlen : base.len cx = .ok (UInt64.ofNat count) := by
    unfold Miri.Interpreter.OpTy.len
    rw [hisSized, hfields]; rfl
  have hcnt32 := hwf.count_lt_two_pow_32
  have hcount_toNat := hwf.uint64_ofNat_count_toNat
  obtain ⟨allocId, tag, baseAddr, relOffset, localAlloc, hprov, _, _, hlive, hbase, _, hptr, _, _,
    _, _, _, _, harr⟩ := hmp
  obtain ⟨_, _, _, hslice⟩ := harr elemKind count elems hwf.arr_kind rfl
  have hlen_elems := hslice.elems_len
  refine ⟨fun hin => ?_, fun hfe hoob hlt64 => ?_⟩
  · have hfrom_le : fromIdx ≤ count := by
      rcases hin with ⟨_, h1, h2⟩ | ⟨_, h1⟩ <;> omega
    have hto_le : toIdx ≤ count := by
      rcases hin with ⟨_, _, h2⟩ | ⟨_, h1⟩ <;> omega
    have hcnt_le : fromIdx + cnt ≤ count := by
      dsimp only [cnt, subsliceEnd]
      rcases hin with ⟨rfl, h1, h2⟩ | ⟨rfl, h1⟩ <;> simp <;> omega
    have hcnt_le' : cnt ≤ count := by omega
    have hfrom_lt64 : fromIdx < 2 ^ 64 := by omega
    have hto_lt64 : toIdx < 2 ^ 64 := by omega
    have hnot_ge64 : ¬(fromIdx ≥ 2 ^ 64 || toIdx ≥ 2 ^ 64) := by
      simp only [GE.ge, Bool.or_eq_true, decide_eq_true_eq, not_or]
      omega
    have hfrom_toNat : (UInt64.ofNat fromIdx).toNat = fromIdx := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hfrom_lt64)]
    have hto_toNat : (UInt64.ofNat toIdx).toNat = toIdx := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hto_lt64)]
    have hcntU_toNat : (UInt64.ofNat cnt).toNat = cnt := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : cnt < 2 ^ 64))]
    have hmul_from : es.mul (UInt64.ofNat fromIdx) =
        .ok (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat fromIdx)) :=
      elemSize_mul_ok hwf hfrom_le
    have hmul_cnt : es.mul (UInt64.ofNat cnt) =
        .ok (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt)) :=
      elemSize_mul_ok hwf hcnt_le'
    have hes16 := hwf.elem_size_le_16
    have hoff_toNat : (es.bytes * UInt64.ofNat fromIdx).toNat = fromIdx * es.bytes.toNat := by
      rw [UInt64.toNat_mul, hfrom_toNat, Nat.mul_comm]
      apply Nat.mod_eq_of_lt
      have hle : fromIdx * es.bytes.toNat ≤ count * es.bytes.toNat := Nat.mul_le_mul_right _ hfrom_le
      have htot := hwf.total_bytes_bound
      dsimp only [es] at hle htot ⊢
      omega
    have hoff_le : (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat fromIdx)).bytes.toNat ≤
        (translateTy arrTy layouts).layout.size.bytes.toNat := by
      show (es.bytes * UInt64.ofNat fromIdx).toNat ≤ _
      rw [hoff_toNat, hwf.arr_size_toNat]
      exact Nat.mul_le_mul_right _ hfrom_le
    have hoff_i64 : (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat fromIdx)).bytes.toNat < 2 ^ 63 := by
      show (es.bytes * UInt64.ofNat fromIdx).toNat < _
      rw [hoff_toNat]
      have hle : fromIdx * es.bytes.toNat ≤ count * es.bytes.toNat := Nat.mul_le_mul_right _ hfrom_le
      have htot := hwf.total_bytes_bound
      dsimp only [es] at hle htot ⊢
      omega
    have hmo := projectionMemoryOffset_inbounds_of_memPlaceRel hnodup
      (MemPlaceRel.mk allocId tag baseAddr relOffset localAlloc hprov (by assumption)
        (by assumption) hlive hbase (by assumption) hptr (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption) (by assumption) harr)
      hoff_le hoff_i64
    have hsublay : cx.subsliceLayout base.layout (UInt64.ofNat cnt) =
        .ok ({ ty := arrLay.ty,
               layout := { arrLay.layout with
                 fields := .Array es (UInt64.ofNat cnt),
                 size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt) } }, .none) := by
      show annealSubsliceLayout arrLay (UInt64.ofNat cnt) = _
      unfold annealSubsliceLayout
      have hf : arrLay.layout.fields = .Array es (UInt64.ofNat count) := hwf.arr_fields
      simp only [hf, hmul_cnt]
    refine ⟨?_, ?_, allocId, tag, baseAddr, relOffset, localAlloc, hprov, hlive, hbase, hptr,
      hslice.subslice hcnt_le⟩
    · simp only [readProjectedValue, extractSubslice_inBounds hlen_elems hin]
      rfl
    · simp only [annealProjectList, Miri.Interpreter.project, hnot_ge64]
      change (do
        let next ← Miri.Interpreter.projectSubslice cx base (UInt64.ofNat fromIdx)
          (UInt64.ofNat toIdx) fromEnd
        Except.ok next) = _
      unfold Miri.Interpreter.projectSubslice Miri.Interpreter.prepareSubslice
      rw [hlen, hfields]
      rcases hin with ⟨rfl, hft, _⟩ | ⟨rfl, hsum⟩
      · have hnot_lt : ¬(UInt64.ofNat toIdx < UInt64.ofNat fromIdx) := by
          simp only [UInt64.lt_iff_toNat_lt, hto_toNat, hfrom_toNat]
          omega
        have hcntU : UInt64.ofNat toIdx - UInt64.ofNat fromIdx = UInt64.ofNat cnt := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_sub_of_le, hto_toNat, hfrom_toNat, hcntU_toNat]
          · simp [cnt, subsliceEnd]
          · simp only [UInt64.le_iff_toNat_le, hto_toNat, hfrom_toNat]
            omega
        simp only [Bool.false_eq_true, ↓reduceIte, hmul_from, Except.mapError, hnot_lt,
          bind, Except.bind, pure, Except.pure, hcntU, hsublay]
        unfold Miri.Interpreter.OpTy.offsetWithMeta
        simp only [cx, base, annealSubsliceProjectionCx, annealProjectionCx, bind, Except.bind,
          pure, Except.pure]
        rw [hmo]
        rfl
      · have hnot_oob : ¬((UInt64.ofNat fromIdx).toNat + (UInt64.ofNat toIdx).toNat ≥ 2 ^ 64 ||
            (UInt64.ofNat fromIdx).toNat + (UInt64.ofNat toIdx).toNat > (UInt64.ofNat count).toNat) := by
          rw [hfrom_toNat, hto_toNat, hcount_toNat]
          simp only [GE.ge, GT.gt, Bool.or_eq_true, decide_eq_true_eq, not_or]
          omega
        have hsub_toNat : (UInt64.ofNat count - UInt64.ofNat toIdx).toNat = count - toIdx := by
          rw [UInt64.toNat_sub_of_le]
          · rw [hcount_toNat, hto_toNat]
          · simp only [UInt64.le_iff_toNat_le, hto_toNat, hcount_toNat, hto_le]
        have hnot_lt : ¬(UInt64.ofNat count - UInt64.ofNat toIdx < UInt64.ofNat fromIdx) := by
          simp only [UInt64.lt_iff_toNat_lt, hsub_toNat, hfrom_toNat]
          omega
        have hcntU : UInt64.ofNat count - UInt64.ofNat toIdx - UInt64.ofNat fromIdx =
            UInt64.ofNat cnt := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_sub_of_le, hsub_toNat, hfrom_toNat, hcntU_toNat]
          · simp [cnt, subsliceEnd]
          · simp only [UInt64.le_iff_toNat_le, hsub_toNat, hfrom_toNat]
            omega
        simp only [↓reduceIte, hnot_oob, Bool.false_eq_true, hmul_from, Except.mapError, hnot_lt,
          bind, Except.bind, pure, Except.pure, hcntU, hsublay]
        unfold Miri.Interpreter.OpTy.offsetWithMeta
        simp only [cx, base, annealSubsliceProjectionCx, annealProjectionCx, bind, Except.bind,
          pure, Except.pure]
        rw [hmo]
        rfl
  · subst hfe
    have hub : readProjectedValue locals (.aggregate 0 elems) [.subslice fromIdx toIdx true] =
        .ub := by
      simp only [readProjectedValue, extractSubslice_fromEnd_oob hlen_elems hoob]
    refine ⟨hub, ?msg, ?eq⟩
    case eq =>
    have hfrom_lt64 : fromIdx < 2 ^ 64 := by omega
    have hto_lt64 : toIdx < 2 ^ 64 := by omega
    have hnot_ge64 : ¬(fromIdx ≥ 2 ^ 64 || toIdx ≥ 2 ^ 64) := by
      simp only [GE.ge, Bool.or_eq_true, decide_eq_true_eq, not_or]
      omega
    have hfrom_toNat : (UInt64.ofNat fromIdx).toNat = fromIdx := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hfrom_lt64)]
    have hto_toNat : (UInt64.ofNat toIdx).toNat = toIdx := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hto_lt64)]
    have hoob' : ((UInt64.ofNat fromIdx).toNat + (UInt64.ofNat toIdx).toNat ≥ 2 ^ 64 ||
        (UInt64.ofNat fromIdx).toNat + (UInt64.ofNat toIdx).toNat > (UInt64.ofNat count).toNat) =
          true := by
      rw [hfrom_toNat, hto_toNat, hcount_toNat]
      simp only [GE.ge, GT.gt, Bool.or_eq_true, decide_eq_true_eq]
      omega
    simp only [annealProjectList, Miri.Interpreter.project, hnot_ge64]
    change (do
      let next ← Miri.Interpreter.projectSubslice cx base (UInt64.ofNat fromIdx)
        (UInt64.ofNat toIdx) true
      Except.ok next).mapError annealLiftProjectionError = _
    unfold Miri.Interpreter.projectSubslice Miri.Interpreter.prepareSubslice
    rw [hlen]
    simp only [↓reduceIte, hoob', bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
      Except.mapError, annealLiftProjectionError]
    rfl

/-! ## 10. Boundaries of the Agreeing Fragment

Outside the fragment above, the two semantics disagree; the theorems below pin
down two such boundaries exactly rather than weakening the correspondence. -/

/-- **Inverted subslice bounds** (ill-formed MIR, which rustc's validator
rejects): for `a[fromIdx..toIdx]` with `toIdx < fromIdx ≤ count`, Anneal reports
undefined behavior, while `lean-miri`'s `prepareSubslice` reports the broken
invariant "subslice length underflow", which `annealLiftProjectionError` maps to
`StepError.invalidProgram`, not to undefined behavior. -/
theorem evalProjection_subslice_inverted_divergence
    {mach : AnnealMachine}
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (locals : List LocalSlot)
    {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {elems : List Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    {fromIdx toIdx : Nat} (hinv : toIdx < fromIdx) (hfrom : fromIdx ≤ count) :
    readProjectedValue locals (.aggregate 0 elems) [.subslice fromIdx toIdx false] = .ub ∧
    (annealProjectList (annealSubsliceProjectionCx frame layouts mach)
        ⟨.indirect mp, translateTy arrTy layouts⟩ [.Subslice fromIdx toIdx false]).mapError
        annealLiftProjectionError =
      .error (.invalidProgram "subslice length underflow") := by
  let cx := annealSubsliceProjectionCx frame layouts mach
  let base : Miri.Interpreter.OpTy AnnealProv := ⟨.indirect mp, translateTy arrTy layouts⟩
  let es := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
  have hfields : base.layout.layout.fields = .Array es (UInt64.ofNat count) := hwf.arr_fields
  have hisSized : base.layout.layout.isSized = true := hwf.arr_isSized
  have hlen : base.len cx = .ok (UInt64.ofNat count) := by
    unfold Miri.Interpreter.OpTy.len
    rw [hisSized, hfields]; rfl
  have hcnt32 := hwf.count_lt_two_pow_32
  have hfrom_lt64 : fromIdx < 2 ^ 64 := by omega
  have hto_lt64 : toIdx < 2 ^ 64 := by omega
  have hnot_ge64 : ¬(fromIdx ≥ 2 ^ 64 || toIdx ≥ 2 ^ 64) := by
    simp only [GE.ge, Bool.or_eq_true, decide_eq_true_eq, not_or]
    omega
  have hfrom_toNat : (UInt64.ofNat fromIdx).toNat = fromIdx := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hfrom_lt64)]
  have hto_toNat : (UInt64.ofNat toIdx).toNat = toIdx := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hto_lt64)]
  have hmul_from : es.mul (UInt64.ofNat fromIdx) =
      .ok (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat fromIdx)) :=
    elemSize_mul_ok hwf hfrom
  have hlt : (UInt64.ofNat toIdx < UInt64.ofNat fromIdx) = True := by
    simp only [UInt64.lt_iff_toNat_lt, hto_toNat, hfrom_toNat, eq_iff_iff, iff_true]
    exact hinv
  refine ⟨?_, ?_⟩
  · simp only [readProjectedValue, extractSubslice_inverted (elems := elems) hinv]
  · simp only [annealProjectList, Miri.Interpreter.project, hnot_ge64]
    change (do
      let next ← Miri.Interpreter.projectSubslice cx base (UInt64.ofNat fromIdx)
        (UInt64.ofNat toIdx) false
      Except.ok next).mapError annealLiftProjectionError = _
    unfold Miri.Interpreter.projectSubslice Miri.Interpreter.prepareSubslice
    rw [hlen, hfields]
    simp only [Bool.false_eq_true, ↓reduceIte, hmul_from, Except.mapError, hlt, bind,
      Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      annealLiftProjectionError]

/-- **Past-end `fromEnd = false` subslice bounds** (ill-formed MIR, which
rustc's validator rejects): for `a[fromIdx..toIdx]` with
`fromIdx ≤ count < toIdx` and `toIdx * elemSize < 2 ^ 64`, Anneal's
`extractSubslice` checks `toIdx ≤ count` and reports undefined behavior, whereas
`lean-miri`'s `prepareSubslice` checks only `fromIdx ≤ toIdx` when
`fromEnd = false` and returns the place at offset `fromIdx * elemSize` with
length `toIdx - fromIdx`. -/
theorem evalProjection_subslice_fromEndFalse_oob_divergence
    {mach : AnnealMachine}
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (locals : List LocalSlot)
    {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {elems : List Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup mach)
    (hmp : MemPlaceRel mach arrTy layouts (some (.aggregate 0 elems)) mp)
    {fromIdx toIdx : Nat} (hfrom : fromIdx ≤ count) (hoob : count < toIdx)
    (hto_mul : toIdx * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat < 2 ^ 64)
    (hto_lt64 : toIdx < 2 ^ 64) :
    let cx := annealSubsliceProjectionCx frame layouts mach
    let arrLay := translateTy arrTy layouts
    let es := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
    let cnt := toIdx - fromIdx
    readProjectedValue locals (.aggregate 0 elems) [.subslice fromIdx toIdx false] = .ub ∧
    annealProjectList cx ⟨.indirect mp, arrLay⟩ [.Subslice fromIdx toIdx false] =
      .ok ⟨.indirect { mp with
              ptr := { mp.ptr with
                offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + es.bytes * UInt64.ofNat fromIdx) },
              metadata := .none },
           { ty := arrLay.ty,
             layout := { arrLay.layout with
               fields := .Array es (UInt64.ofNat cnt),
               size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt) } }⟩ := by
  intro cx arrLay es cnt
  let base : Miri.Interpreter.OpTy AnnealProv := ⟨.indirect mp, arrLay⟩
  have hfields : base.layout.layout.fields = .Array es (UInt64.ofNat count) := hwf.arr_fields
  have hisSized : base.layout.layout.isSized = true := hwf.arr_isSized
  have hlen : base.len cx = .ok (UInt64.ofNat count) := by
    unfold Miri.Interpreter.OpTy.len
    rw [hisSized, hfields]; rfl
  obtain ⟨allocId, tag, baseAddr, relOffset, localAlloc, hprov, _, _, hlive, hbase, _, hptr, _, _,
    _, _, _, _, harr⟩ := hmp
  obtain ⟨_, _, _, hslice⟩ := harr elemKind count elems hwf.arr_kind rfl
  have hlen_elems : length elems = count := hslice.elems_len
  have hble : Nat.ble toIdx count = false := by
    cases h : Nat.ble toIdx count with
    | false => rfl
    | true => exact absurd (Nat.le_of_ble_eq_true h) (by omega)
  have hcnt32 := hwf.count_lt_two_pow_32
  have hfrom_lt64 : fromIdx < 2 ^ 64 := by omega
  have hnot_ge64 : ¬(fromIdx ≥ 2 ^ 64 || toIdx ≥ 2 ^ 64) := by
    simp only [GE.ge, Bool.or_eq_true, decide_eq_true_eq, not_or]
    omega
  have hfrom_toNat : (UInt64.ofNat fromIdx).toNat = fromIdx := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hfrom_lt64)]
  have hto_toNat : (UInt64.ofNat toIdx).toNat = toIdx := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hto_lt64)]
  have hcnt_lt64 : cnt < 2 ^ 64 := by omega
  have hcntU_toNat : (UInt64.ofNat cnt).toNat = cnt := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hcnt_lt64)]
  have hmul_from : es.mul (UInt64.ofNat fromIdx) =
      .ok (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat fromIdx)) :=
    elemSize_mul_ok hwf hfrom
  have hmul_cnt : es.mul (UInt64.ofNat cnt) =
      .ok (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt)) := by
    have hmul_lt64 : es.bytes.toNat * (UInt64.ofNat cnt).toNat < 2 ^ 64 := by
      rw [hcntU_toNat, Nat.mul_comm]
      have hle : cnt * es.bytes.toNat ≤ toIdx * es.bytes.toNat := Nat.mul_le_mul_right _ (by omega)
      dsimp only [es] at hle ⊢
      omega
    unfold Miri.ABI.Size.mul
    dsimp only
    have hcond :
        (UInt64.ofNat cnt != 0 &&
          es.bytes * UInt64.ofNat cnt / UInt64.ofNat cnt != es.bytes) = false := by
      by_cases hz : UInt64.ofNat cnt = 0
      · simp [hz]
      · have hpos : 0 < (UInt64.ofNat cnt).toNat :=
          Nat.pos_of_ne_zero (fun h0 => hz (UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h0)))
        have hprod_toNat :
            (es.bytes * UInt64.ofNat cnt).toNat = es.bytes.toNat * (UInt64.ofNat cnt).toNat := by
          rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by simpa [UInt64.size] using hmul_lt64)]
        have hdiv : es.bytes * UInt64.ofNat cnt / UInt64.ofNat cnt = es.bytes := by
          apply UInt64.eq_of_toBitVec_eq
          apply BitVec.eq_of_toNat_eq
          change ((es.bytes * UInt64.ofNat cnt) / UInt64.ofNat cnt).toNat = es.bytes.toNat
          rw [UInt64.toNat_div, hprod_toNat, Nat.mul_div_left _ hpos]
        simp [hdiv]
    rw [hcond]
    rfl
  have hoff_toNat : (es.bytes * UInt64.ofNat fromIdx).toNat = fromIdx * es.bytes.toNat := by
    rw [UInt64.toNat_mul, hfrom_toNat, Nat.mul_comm]
    apply Nat.mod_eq_of_lt
    have hle : fromIdx * es.bytes.toNat ≤ count * es.bytes.toNat := Nat.mul_le_mul_right _ hfrom
    have htot := hwf.total_bytes_bound
    dsimp only [es] at hle htot ⊢
    omega
  have hoff_le : (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat fromIdx)).bytes.toNat ≤
      (translateTy arrTy layouts).layout.size.bytes.toNat := by
    show (es.bytes * UInt64.ofNat fromIdx).toNat ≤ _
    rw [hoff_toNat, hwf.arr_size_toNat]
    exact Nat.mul_le_mul_right _ hfrom
  have hoff_i64 : (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat fromIdx)).bytes.toNat < 2 ^ 63 := by
    show (es.bytes * UInt64.ofNat fromIdx).toNat < _
    rw [hoff_toNat]
    have hle : fromIdx * es.bytes.toNat ≤ count * es.bytes.toNat := Nat.mul_le_mul_right _ hfrom
    have htot := hwf.total_bytes_bound
    dsimp only [es] at hle htot ⊢
    omega
  have hmo := projectionMemoryOffset_inbounds_of_memPlaceRel hnodup
    (MemPlaceRel.mk allocId tag baseAddr relOffset localAlloc hprov (by assumption)
      (by assumption) hlive hbase (by assumption) hptr (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) harr)
    hoff_le hoff_i64
  have hsublay : cx.subsliceLayout base.layout (UInt64.ofNat cnt) =
      .ok ({ ty := arrLay.ty,
             layout := { arrLay.layout with
               fields := .Array es (UInt64.ofNat cnt),
               size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt) } }, .none) := by
    show annealSubsliceLayout arrLay (UInt64.ofNat cnt) = _
    unfold annealSubsliceLayout
    have hf : arrLay.layout.fields = .Array es (UInt64.ofNat count) := hwf.arr_fields
    simp only [hf, hmul_cnt]
  have hnot_lt : ¬(UInt64.ofNat toIdx < UInt64.ofNat fromIdx) := by
    simp only [UInt64.lt_iff_toNat_lt, hto_toNat, hfrom_toNat]
    omega
  have hcntU : UInt64.ofNat toIdx - UInt64.ofNat fromIdx = UInt64.ofNat cnt := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le, hto_toNat, hfrom_toNat, hcntU_toNat]
    simp only [UInt64.le_iff_toNat_le, hto_toNat, hfrom_toNat]
    omega
  refine ⟨?_, ?_⟩
  · simp only [readProjectedValue, extractSubslice, hlen_elems, hble]
  · simp only [annealProjectList, Miri.Interpreter.project, hnot_ge64]
    change (do
      let next ← Miri.Interpreter.projectSubslice cx base (UInt64.ofNat fromIdx)
        (UInt64.ofNat toIdx) false
      Except.ok next) = _
    unfold Miri.Interpreter.projectSubslice Miri.Interpreter.prepareSubslice
    rw [hlen, hfields]
    simp only [Bool.false_eq_true, ↓reduceIte, hmul_from, Except.mapError, hnot_lt,
      bind, Except.bind, pure, Except.pure, hcntU, hsublay]
    unfold Miri.Interpreter.OpTy.offsetWithMeta
    simp only [cx, base, annealSubsliceProjectionCx, annealProjectionCx, bind, Except.bind,
      pure, Except.pure]
    rw [hmo]
    rfl

/-- **`evalRvalue_union_aggregate_activeField_simulation`** (`D13a` upgrade of
`evalRvalue_union_aggregate_activeField_ignored`): `evalRvalue` on a union
aggregate `Rvalue.aggregate (.adt d 0 (some f)) [op]` for ANY valid field
`f < n` evaluates `op` and constructs the `.unit`-padded `n`-slot union value
`.aggregate 0 (unionSlotFields n f (.scalar sc))` whose active slot `f` holds
`.scalar sc` and whose sibling slots `j ≠ f` hold `.unit`, instead of ignoring
`activeField`. This is the Anneal-side evaluation half of the `D13a` upgrade;
the two-machine lockstep statement (`lean-miri`'s `writeAggregate` projecting to
field `f` and writing `sc` into bytes `[0, k)`) is
`step_union_aggregate_simulation`, and the lockstep reads of the resulting union
(same-field, narrower/equal cross-field type punning, and wider-field `.ub` on
the uninitialized tail) are `step_union_field_read_simulation`,
`step_union_type_punning_read_simulation`, and
`union_uninit_bytes_read_ub_simulation`. -/
theorem evalRvalue_union_aggregate_activeField_simulation
    {body : CapturedMir} {locals : List LocalSlot} {mem : Memory}
    (hbor : mem.borrows = .nil) (hcaller : mem.callerLocals = .nil)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {u : Local} {uDecl : LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {d : DefPath} (hadt : ∃ args, uDecl.ty.kind = .adt d args)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl)
    {fTy : Ty} (hprim : IsPrimScalarTy fTy)
    (hfl_sz : fl.layout.size = (translateTy fTy body.layouts).layout.size)
    {op : MirAst.Operand} (hop : WellTypedScalarOperand body tf op fTy)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hok : evalOperand locals op .nil mem.globals body.layouts .nil = .ok (.scalar sc) locals)
    (himm : ImmediateRel fTy body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)))
    (hdecls_adt : ∀ l ∈ collectAdtLayoutsInDecls body.layouts d body.localDecls,
      body.layouts.lookup uDecl.ty.layoutIdx = some l := by
        simp [collectAdtLayoutsInDecls, collectAdtLayoutsInTyAux, stringEq,
          LayoutTable.lookup, get?]) :
    evalRvalue locals (.aggregate (.adt d 0 (some f)) [op]) mem body.localDecls body.layouts =
      .ok (.aggregate 0 (unionSlotFields n f (.scalar sc))) locals mem ∧
    get? (unionSlotFields n f (.scalar sc)) f = some (.scalar sc) ∧
    ∀ j < n, j ≠ f → get? (unionSlotFields n f (.scalar sc)) j = some .unit :=
  ⟨(evalRvalue_unionAggregate_activeField_eq hbor hcaller hdecl_u hadt hwt hfields hf hfl hprim
      hfl_sz hop hdecls_adt).2 sc msc hok himm,
   unionSlotFields_get_self hf (.scalar sc),
   fun _ hj hjne => unionSlotFields_get_ne hf hj hjne (.scalar sc)⟩

/-! ## 11. Union Field Writes (`step_union_field_write_simulation` & `step_union_field_write_uninit_simulation`)

A write `_u.f = op` to active field `f` of a union that already holds field `f`'s
value rewrites the bytes `[0, k)` in place (`step_union_field_write_simulation`);
and a write `_u.j = op` (`j < n`) to a union that is still `.uninit` initializes
the union in Anneal (`uninitFieldWriteShell?` + `writeProjectedForLocal`) while
moving `_u` to a fresh stack allocation via `forceAllocation` and writing `[0, k)`
in `lean-miri` (`step_union_field_write_uninit_simulation`). -/

/-- `annealEvalUnionFieldPlace` on a memory-backed union local caches the
local's layout and returns the place of field `j` at offset `0`. -/
theorem annealEvalUnionFieldPlace_indirect
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame])
    {u : Nat} {uDecl : LocalDecl} (hlt : u < topFrame.locals.size)
    (hdecl : get? body.localDecls u = some uDecl)
    (hcache : ∀ l, (topFrame.locals[u]'hlt).layout = some l →
      l = translateTy uDecl.ty body.layouts)
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hval : (topFrame.locals[u]'hlt).value = .live (.indirect mp))
    (hmeta : mp.metadata = .none)
    {n j : Nat} (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hj : j < n) {fty : Ty} (hprim : IsPrimScalarTy fty) :
    annealEvalUnionFieldPlace body.localDecls body.layouts u j (encodeTyId fty) m =
      .ok ⟨.memory mp, translateTy fty body.layouts⟩
        { m with stack := ⟨#[cacheFrameLocalLayout topFrame u hlt
          (translateTy uDecl.ty body.layouts)]⟩ } := by
  have hres := annealResolveAndCacheLocalLayout_eq (known := none) hframes hlt hdecl hcache
  have hgo : (cacheFrameLocalLayout topFrame u hlt
      (translateTy uDecl.ty body.layouts)).getLocalOperand u = .ok (.indirect mp) := by
    apply frame_getLocalOperand_live
    rw [cacheFrameLocalLayout_getLocal]
    rw [← hval]
  have hproj := projectField_union
    (cacheFrameLocalLayout topFrame u hlt (translateTy uDecl.ty body.layouts))
    body.layouts m.machine hfields hj hprim hmeta
  unfold annealEvalUnionFieldPlace
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone_some,
    Bool.false_eq_true, ↓reduceIte, hres, hgo, pure, EStateM.pure]
  simp only [stack_currentFrame?_singleton _
    (cacheFrameLocalLayout topFrame u hlt (translateTy uDecl.ty body.layouts)) rfl]
  rw [hproj]
  rfl

/-- Evaluating a scalar constant or `copy` of an immediate scalar local under
`FrameRelLM2_4`: both machines report undefined behavior (`lean-miri` once the
operand is read), or both produce related scalars, and `lean-miri` only caches
the copied local's layout, leaving every memory-backed local untouched. -/
theorem evalScalarOperand_LM2_4
    {body : CapturedMir} {mach : AnnealMachine} {af : StackFrame}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (hframe : FrameRelLM2_4 body mach af tf)
    (hprim : IsPrimScalarTy ty)
    (hop : WellTypedScalarOperand body tf op ty)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    let st : AnnealStepState := { stack := ⟨#[tf]⟩, machine := mach }
    (evalOperand af.locals op .nil globals body.layouts .nil = .ub ∧
      ((∃ m' msg,
        annealEvalOperand body.localDecls body.layouts (translateOperand op) known st =
          .error (.undefinedBehavior msg) m') ∨
       (∃ lay st', annealEvalOperand body.localDecls body.layouts (translateOperand op) known st =
          .ok ⟨.immediate .uninit, lay⟩ st'))) ∨
    (∃ sc msc tf',
      evalOperand af.locals op .nil globals body.layouts .nil = .ok (.scalar sc) af.locals ∧
      annealEvalOperand body.localDecls body.layouts (translateOperand op) known st =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy ty body.layouts⟩
          { stack := ⟨#[tf']⟩, machine := mach } ∧
      FrameRelLM2_4 body mach af tf' ∧
      (MemoryAllocDisjoint tf → MemoryAllocDisjoint tf') ∧
      (∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
      tf' = { tf with locals := tf'.locals } ∧
      (∀ (j : Nat) (mp : Miri.Interpreter.MemPlace AnnealProv)
        (c : Option Miri.Interpreter.LocalLayout),
        tf.locals[j]? = some ⟨.live (.indirect mp), c⟩ → tf'.locals[j]? = tf.locals[j]?) ∧
      ScalarRel sc msc ∧
      ImmediateRel ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc))) := by
  dsimp only
  let st : AnnealStepState := { stack := ⟨#[tf]⟩, machine := mach }
  cases hop with
  | constScalar c sc hval hprim_c hsz hcan hlaysz hbool hchar =>
    obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
    have heval_a : evalOperand af.locals (.constant c) .nil globals body.layouts .nil =
        .ok (.scalar sc) af.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    have heval_m : annealEvalOperand body.localDecls body.layouts
        (translateOperand (.constant c)) known st =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ st := by
      with_unfolding_all
        unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
        dsimp only
        rw [hval]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton st.stack tf rfl, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry, hprim_c.layoutOfEncoded]
    exact Or.inr ⟨sc, msc, tf, heval_a, heval_m, hframe, id, (fun _ h => h), rfl,
      (fun _ _ _ _ => rfl), hrel, .scalar sc msc hrel hlaysz hbool hchar⟩
  | copyLocal idx decl hdecl hsz_nz himm =>
    obtain ⟨slot, mls, _, hlt_idx, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
    have himm' := himm mls hmls
    have hloc' : LocalRel mach decl body.layouts slot mls := by
      cases hloc with
      | base _ _ hl => exact hl
      | union _ _ _ _ _ mp' _ _ _ _ _ _ => exact absurd rfl (himm' mp')
    have htr : translateOperand (.copy ⟨idx, .nil⟩) = .Copy ⟨idx, #[]⟩ := rfl
    rw [htr]
    cases hloc' with
    | dead cachedLayout hcache =>
      left
      have hdead := annealEvalOperand_copy_dead (m := st) (topFrame := tf) (known := known)
        rfl hlt_idx hdecl hmls_eq hcache
      exact ⟨by simp [evalOperand, hslot], Or.inl ⟨_, _, hdead⟩⟩
    | indirect _ mp' _ _ _ _ =>
      exact False.elim (himm' mp' rfl)
    | immediate _ imm cachedLayout hcache hval =>
      have hlive := annealEvalOperand_copy_live (m := st) (topFrame := tf) (known := known)
        rfl hlt_idx hdecl hmls_eq hcache
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · left
        exact ⟨by simp [evalOperand, hslot], Or.inr ⟨_, _, hlive⟩⟩
      · right
        obtain ⟨sc, msc, rfl, rfl, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩ :=
          himmRel.of_primitive_scalar hprim
        have ha : evalOperand af.locals (.copy ⟨idx, .nil⟩) .nil globals body.layouts .nil =
            .ok (.scalar sc) af.locals := by
          simp [evalOperand, readProjectedValue, hslot]
        let tf' := cacheFrameLocalLayout tf idx hlt_idx (translateTy decl.ty body.layouts)
        refine ⟨sc, msc, tf', ha, hlive, hframe.cache_local_layout hdecl hlt_idx, ?_,
          (fun _ hj => hj.cache_layout hlt_idx _), rfl, ?_, hrel_sc,
          .scalar sc msc hrel_sc hsz_sc hbool_sc hchar_sc⟩
        · intro hdisj
          apply MemoryAllocDisjoint.mono_layout hdisj
          intro k
          by_cases hk : k = idx
          · subst hk
            exists (translateTy decl.ty body.layouts)
            dsimp [tf', cacheFrameLocalLayout]
            rw [Array.getElem?_set]
            simp only [↓reduceIte]
            simp [hmls, hmls_eq]
          · exists (tf.locals[k]?).bind (fun x => x.layout)
            dsimp [tf', cacheFrameLocalLayout]
            rw [Array.getElem?_set_ne _ (Ne.symm hk)]
            cases tf.locals[k]? <;> rfl
        · intro j mp_j c_j hj
          have hne : j ≠ idx := by
            intro h
            subst h
            rw [hmls] at hj
            injection hj with hj
            exact himm' mp_j (by rw [hj])
          dsimp [tf', cacheFrameLocalLayout]
          rw [Array.getElem?_set_ne _ (Ne.symm hne)]

/-- `MemPlaceRel` depends on the machine only through its own allocation entry
and that allocation's base address. -/
theorem MemPlaceRel.of_entry {mach mach' : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {optVal : Option Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hent : ∀ a la, mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some a →
      (a, la) ∈ mach.memory.live.toList →
      (a, la) ∈ mach'.memory.live.toList ∧ mach'.lookupBaseAddr a = mach.lookupBaseAddr a)
    (h : MemPlaceRel mach ty layouts optVal mp) : MemPlaceRel mach' ty layouts optVal mp := by
  cases h with
  | mk allocId tag baseAddr relOffset localAlloc hprov hmis hmeta hl hb hovf hptr hmut halign
      hbounds huninit hval hscalar harray =>
    obtain ⟨hl', hb'⟩ := hent allocId localAlloc (by rw [hprov]; rfl) hl
    exact .mk allocId tag baseAddr relOffset localAlloc hprov hmis hmeta hl'
      (by rw [hb']; exact hb) hovf hptr hmut halign hbounds huninit hval hscalar harray

/-- `UnionMemRel` depends on the machine only through its own allocation entry
and that allocation's base address. -/
theorem UnionMemRel.of_entry {mach mach' : AnnealMachine} {uTy : Ty} {layouts : LayoutTable}
    {S : Nat} {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hent : ∀ a la, mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some a →
      (a, la) ∈ mach.memory.live.toList →
      (a, la) ∈ mach'.memory.live.toList ∧ mach'.lookupBaseAddr a = mach.lookupBaseAddr a)
    (h : UnionMemRel mach uTy layouts S f0Ty sc mp) :
    UnionMemRel mach' uTy layouts S f0Ty sc mp := by
  cases h with
  | mk allocId tag baseAddr localAlloc msc hprov hmis hmeta hl hb hptr hovf hsz hlen hmut hp hal
      hex hnat hk hmask hrel hprim himm hraw =>
    obtain ⟨hl', hb'⟩ := hent allocId localAlloc (by rw [hprov]; rfl) hl
    exact .mk allocId tag baseAddr localAlloc msc hprov hmis hmeta hl' (by rw [hb']; exact hb)
      hptr hovf hsz hlen hmut hp hal hex hnat hk hmask hrel hprim himm hraw

/-- `UnionLocalRel` depends on the machine only through the allocation entry of
a memory-backed local and that allocation's base address. -/
theorem UnionLocalRel.of_entry {mach mach' : AnnealMachine} {decl : LocalDecl}
    {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (hent : ∀ mp c, mls = ⟨.live (.indirect mp), c⟩ →
      ∀ a la, mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some a →
        (a, la) ∈ mach.memory.live.toList →
        (a, la) ∈ mach'.memory.live.toList ∧ mach'.lookupBaseAddr a = mach.lookupBaseAddr a)
    (h : UnionLocalRel mach decl layouts slot mls) :
    UnionLocalRel mach' decl layouts slot mls := by
  cases h with
  | base _ _ hl =>
    cases hl with
    | dead c hc => exact .base _ _ (.dead c hc)
    | immediate slot imm c hc hv => exact .base _ _ (.immediate slot imm c hc hv)
    | indirect slot mp c hc hne hmp =>
      exact .base _ _ (.indirect slot mp c hc hne (hmp.of_entry (hent mp c rfl)))
  | union S n f f0Ty sc mp c hc hwt hfields hf hmem =>
    exact .union S n f f0Ty sc mp c hc hwt hfields hf (hmem.of_entry (hent mp c rfl))

/-- Writing a scalar `msc'` of width `sc'.sizeBytes ≥ sc_old.sizeBytes` (`≤ S`)
at offset `0` of an existing `UnionMemRel` allocation updates the allocation in
place to `UnionMemRel` for `(f0Ty, sc')` (`IsUnionPrefixMask S sc'.sizeBytes`). -/
theorem annealWriteImmediate_unionInplace_ge
    {mach : AnnealMachine} (hnodup : LiveAllocsNodup mach)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {destLay : Miri.Interpreter.LocalLayout}
    {uTy : Ty} {layouts : LayoutTable} {S : Nat} {f0Ty_old f0Ty : Ty} {sc_old : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hmem : UnionMemRel mach uTy layouts S f0Ty_old sc_old mp) (hS : ValidScalarBytes S)
    (hprim : IsPrimScalarTy f0Ty)
    {sc' : MirAst.ScalarInt} {msc' : Miri.Memory.ScalarInt} (hrel' : ScalarRel sc' msc')
    (hk_ge : sc_old.sizeBytes ≤ sc'.sizeBytes) (hk'S : sc'.sizeBytes ≤ S)
    (hf0imm' : ImmediateRel f0Ty layouts (.scalar sc') (.scalar (.fromScalarInt msc'))) :
    ∃ (allocIdx : Nat) (allocId : Miri.Memory.AllocId)
      (kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind)
      (A' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
      (la₀ : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind),
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some allocId ∧
      (allocId, la₀) ∈ mach.memory.live.toList ∧
      annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc')) ⟨.memory mp, destLay⟩
          { stack := ⟨#[tf]⟩, machine := mach } =
        .ok () { stack := ⟨#[tf]⟩, machine := inplaceMachine mach allocIdx allocId kind A' } ∧
      UnionMemRel (inplaceMachine mach allocIdx allocId kind A') uTy layouts S f0Ty sc' mp ∧
      LiveAllocsNodup (inplaceMachine mach allocIdx allocId kind A') ∧
      (∀ a la, a ≠ allocId → (a, la) ∈ mach.memory.live.toList →
        (a, la) ∈ (inplaceMachine mach allocIdx allocId kind A').memory.live.toList) := by
  cases hmem with
  | mk allocId tag baseAddr la msc hprov hmis hmeta hlive hbase hptr hovf hsz hlen hmut hp hal
      hex hnat _ hmask hrel _ _ _ =>
  obtain ⟨allocIdx, _, hfindIdx, hget, hset⟩ := array_findIdx?_of_nodup_fst hnodup hlive
  rcases la with ⟨kind, A⟩
  have hS16 : S ≤ 16 := by rcases hS with h | h | h | h | h <;> omega
  obtain ⟨M', hset_mask, hM'⟩ := hmask.setRange_ge hS hrel.validBytes hrel'.validBytes hk_ge hk'S
  obtain ⟨A', hw, hA'_sz, hA'_len, hA'_align, hA'_mut, hA'_prov, hA'_mask, hA'_extra,
    hA'_native, hA'_raw⟩ := union_writeScalar_prefix hrel' hlen hsz hS16 hk'S hmut hp hset_mask
  have hoff : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = Miri.ABI.Size.ZERO := by
    rw [hptr]; simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
  have hmsc_sz : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc').size = msc'.size :=
    rfl
  obtain ⟨hnodup', hmem', hother⟩ := hset ⟨kind, A'⟩
  refine ⟨allocIdx, allocId, kind, A', ⟨kind, A⟩, by rw [hprov]; rfl, hlive, ?_, ?_, hnodup',
    fun a la hne hmem_a => hother a la hne hmem_a⟩
  · unfold annealWriteImmediateLM2_2 annealWriteIndirectImmediate
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      stack_currentFrame?_singleton ⟨#[tf]⟩ tf rfl, hprov, Option.bind,
      Miri.Memory.Provenance.getAllocId, hbase, add_size_zero_bytes, hoff, hfindIdx, hget,
      hmsc_sz, hw, pure, EStateM.pure, set, MonadStateOf.set, EStateM.set]
    rfl
  · exact .mk allocId tag baseAddr ⟨kind, A'⟩ msc' hprov hmis hmeta hmem' hbase hptr hovf
      (hA'_sz.trans hsz) hA'_len hA'_mut hA'_prov (hA'_align.trans hal) (hA'_extra.trans hex)
      (hA'_native.trans hnat) hk'S (hA'_mask ▸ hM') hrel' hprim hf0imm' hA'_raw

/-- Writing a related scalar of field `0`'s size at offset `0` of a union that
`UnionMemRel` relates updates its allocation in place. -/
theorem annealWriteImmediate_unionInplace
    {mach : AnnealMachine} (hnodup : LiveAllocsNodup mach)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {destLay : Miri.Interpreter.LocalLayout}
    {uTy : Ty} {layouts : LayoutTable} {S : Nat} {f0Ty : Ty} {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hmem : UnionMemRel mach uTy layouts S f0Ty sc mp) (hS : ValidScalarBytes S)
    {sc' : MirAst.ScalarInt} {msc' : Miri.Memory.ScalarInt} (hrel' : ScalarRel sc' msc')
    (hk' : sc'.sizeBytes = sc.sizeBytes)
    (hf0imm' : ImmediateRel f0Ty layouts (.scalar sc') (.scalar (.fromScalarInt msc'))) :
    ∃ (allocIdx : Nat) (allocId : Miri.Memory.AllocId)
      (kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind)
      (A' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
      (la₀ : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind),
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some allocId ∧
      (allocId, la₀) ∈ mach.memory.live.toList ∧
      annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc')) ⟨.memory mp, destLay⟩
          { stack := ⟨#[tf]⟩, machine := mach } =
        .ok () { stack := ⟨#[tf]⟩, machine := inplaceMachine mach allocIdx allocId kind A' } ∧
      UnionMemRel (inplaceMachine mach allocIdx allocId kind A') uTy layouts S f0Ty sc' mp ∧
      LiveAllocsNodup (inplaceMachine mach allocIdx allocId kind A') ∧
      (∀ a la, a ≠ allocId → (a, la) ∈ mach.memory.live.toList →
        (a, la) ∈ (inplaceMachine mach allocIdx allocId kind A').memory.live.toList) := by
  have hk_S : sc'.sizeBytes ≤ S := by
    rw [hk']; cases hmem with | mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk _ _ _ _ _ => exact hk
  have hprim0 : IsPrimScalarTy f0Ty := by
    cases hmem with | mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp _ _ => exact hp
  exact annealWriteImmediate_unionInplace_ge hnodup hmem hS hprim0 hrel'
    (Nat.le_of_eq hk'.symm) hk_S hf0imm'

/-- **`step_union_field_write_simulation`** (`LM-2.4`): the projected write
`_u.f = op` of a scalar constant or `copy` of an immediate scalar local into
active field `f` (`f < n`) of a union that holds field `f`'s value `sc`
(`UnionMemRel`).

Both machines report undefined behavior when `op` reads an uninitialized or dead
local, and otherwise both step to related states: Anneal stores
`.aggregate 0 (unionSlotFields n f (.scalar sc'))`, and `lean-miri` rewrites the
bytes `[0, k)` of the union's allocation in place, keeping the bytes `[k, S)`
uninitialized (`UnionMemRel` with `sc'`). -/
theorem step_union_field_write_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {u : Local} {f : Nat} {f0Ty : Ty} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, [.field f f0Ty]⟩ (.use op), span⟩)
    {uDecl : LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {S n : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op f0Ty)
    (hfl : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size := by exact ⟨_, rfl, rfl⟩) :
    StepRelLM2_4 body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      ∃ (sc' : MirAst.ScalarInt) (m' : AnnealStepState)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
          .ok (.scalar sc') s.frame.locals ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals u =
          some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc')))) ∧
        (∀ j, j ≠ u → get? s'.frame.locals j = get? s.frame.locals j) ∧
        m'.stack.frames = #[tf'] ∧
        (∃ c, tf'.locals[u]? = some ⟨.live (.indirect mp), c⟩) ∧
        UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty sc' mp ∧
        LiveAllocsNodup m'.machine ∧
        (∀ tf, m.stack.frames = #[tf] → ∀ j,
          IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
        s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
        StepPreservesHighWater m 0 (m', .ok true)) := by
  rcases hstate with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have hop_tf := hop topFrame hframes
  have hop_ld := hop_tf.evalOperand_localDecls_eq s.frame.locals s.memory.globals
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem; dsimp only at hbor hprot; subst hbor hprot; rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨u, [.field f f0Ty]⟩ (.use op), span⟩ body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
  obtain ⟨c_u, hmls_u⟩ := hu_mls topFrame hframes
  obtain ⟨_, mls_u, hlt_af_u, hlt_u, _, hmls_u', hmls_u_eq, hloc_u⟩ := hframe.lookup_local hdecl_u
  rw [hmls_u] at hmls_u'; injection hmls_u' with hmls_u'; subst hmls_u'
  have hcache_u := hloc_u.layout_eq
  obtain ⟨msc0, hmeta, hk_le0, hprim0, himm0⟩ :
      ∃ msc0, mp.metadata = .none ∧ sc.sizeBytes ≤ S ∧ IsPrimScalarTy f0Ty ∧
        ImmediateRel f0Ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc0)) := by
    cases hmem with
    | mk _ _ _ _ msc0 _ _ hm _ _ _ _ _ _ _ _ _ _ _ hkle _ _ hp0 hi0 _ =>
      exact ⟨msc0, hm, hkle, hp0, hi0⟩
  obtain ⟨hf0sz, hkv⟩ := hmem.f0_size
  have hS := hwt.size_valid
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame u hlt_u layU
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  have hplace : annealEvalUnionFieldPlace body.localDecls body.layouts u f (encodeTyId f0Ty) m =
      .ok ⟨.memory mp, translateTy f0Ty body.layouts⟩ m₀ :=
    annealEvalUnionFieldPlace_indirect hframes hlt_u hdecl_u (by rw [hmls_u_eq]; exact hcache_u)
      (by rw [hmls_u_eq]) hmeta hfields hf hprim0
  have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
  have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
      ⟨u, #[.Field f (encodeTyId f0Ty)]⟩ true m =
      .ok ⟨.memory mp, translateTy f0Ty body.layouts⟩ m₀ := by
    show annealEvalPlaceLM2_4 body.localDecls body.layouts ⟨u, #[.Field f (encodeTyId f0Ty)]⟩ m = _
    simp only [annealEvalPlaceLM2_4, hunion, ↓reduceIte]
    exact hplace
  have hframe₀ : FrameRelLM2_4 body m.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_u hlt_u
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ := hdisj.cache_layout hlt_u _
  have hop₀ : WellTypedScalarOperand body topFrame₀ op f0Ty :=
    hop_tf.cache_layout hlt_u layU
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨u, #[.Field f (encodeTyId f0Ty)]⟩
      (translateRvalue (.use op)) = true := by
    simp [lm24Assign, lm24Place, hunion]
  have hm_pre : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨u, [.field f f0Ty]⟩ (.use op), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
          (some (translateTy f0Ty body.layouts)) >>= fun o =>
          (annealRvalueHooksLM2_4 body.localDecls body.layouts).copyOp () o
            ⟨.memory mp, translateTy f0Ty body.layouts⟩) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateProjectionElem]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace']
    dsimp only [translateRvalue]
    rfl
  have hlm_eq : ∀ st, annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
      (some (translateTy f0Ty body.layouts)) st =
      annealEvalOperand body.localDecls body.layouts (translateOperand op)
        (some (translateTy f0Ty body.layouts)) st := fun st => by
    rw [annealEvalOperandLM2_4_scalar hop₀]
  have hcopy_imm : ∀ (imm : Miri.Interpreter.Immediate AnnealProv)
      (lay : Miri.Interpreter.LocalLayout) (st : AnnealStepState),
      (annealRvalueHooksLM2_4 body.localDecls body.layouts).copyOp () ⟨.immediate imm, lay⟩
          ⟨.memory mp, translateTy f0Ty body.layouts⟩ st =
        (annealReadImmediateLM2_2 ⟨.immediate imm, lay⟩ >>= fun i =>
          annealWriteImmediateLM2_2 i.imm ⟨.memory mp, translateTy f0Ty body.layouts⟩) st := by
    intro imm lay st
    rfl
  rcases evalScalarOperand_LM2_4 hframe₀ hprim0 hop₀ s.memory.globals
      (some (translateTy f0Ty body.layouts)) with
    ⟨ha_ub, ⟨m_err, msg, hm_err⟩ | ⟨lay, st', hm_uninit⟩⟩ |
    ⟨sc', msc', tf₁, ha_ok, hm_ok, hframe₁, hdisj₁, hmono₁, htf₁, hind₁, hrel', himm'⟩
  · -- `op` reads a dead local.
    have ha : evalStmt s ⟨.assign ⟨u, [.field f f0Ty]⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue; dsimp only; rw [hbor, hcaller, hop_ld, ha_ub]
    have hm_err' : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        (some (translateTy f0Ty body.layouts)) m₀ = .error (.undefinedBehavior msg) m_err := by
      rw [hlm_eq]; exact hm_err
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, [.field f f0Ty]⟩ (.use op), span⟩) m =
        (m_err, .error (.undefinedBehavior msg)) := by
      rw [hm_pre]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error hm_err']
    rw [hstep_a, ha, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_stmt]
    exact ⟨.ub _ _, fun _ h => absurd h MirStepNode_fail_ne_step⟩
  · -- `op` reads an uninitialized local.
    have ha : evalStmt s ⟨.assign ⟨u, [.field f f0Ty]⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue; dsimp only; rw [hbor, hcaller, hop_ld, ha_ub]
    have hm_uninit' : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        (some (translateTy f0Ty body.layouts)) m₀ = .ok ⟨.immediate .uninit, lay⟩ st' := by
      rw [hlm_eq]; exact hm_uninit
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, [.field f f0Ty]⟩ (.use op), span⟩) m =
        (st', .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_pre]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hm_uninit', hcopy_imm]
      rfl
    rw [hstep_a, ha, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_stmt]
    exact ⟨.ub _ _, fun _ h => absurd h MirStepNode_fail_ne_step⟩
  · -- `op` evaluates to `sc'`: rewrite field `f` in place.
    cases himm' with
    | scalar _ _ hrel'_sc hsz' hbool' hchar' =>
    have himm' : ImmediateRel f0Ty body.layouts (.scalar sc') (.scalar (.fromScalarInt msc')) :=
      .scalar sc' msc' hrel'_sc hsz' hbool' hchar'
    have hk' : sc'.sizeBytes = sc.sizeBytes :=
      translateSizeBytes_inj hrel'.validBytes hkv (hsz'.symm.trans hf0sz)
    obtain ⟨allocIdx, allocId, kind, A', la₀, hprov_a, hlive₀, hw, hmem', hnodup', hother⟩ :=
      annealWriteImmediate_unionInplace (tf := tf₁) (destLay := translateTy f0Ty body.layouts)
        hnodup hmem hS hrel' hk' himm'
    let mach₃ := inplaceMachine m.machine allocIdx allocId kind A'
    have hm_ok' : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        (some (translateTy f0Ty body.layouts)) m₀ =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc')), translateTy f0Ty body.layouts⟩
          { stack := ⟨#[tf₁]⟩, machine := m.machine } := by
      rw [hlm_eq]; exact hm_ok
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, [.field f f0Ty]⟩ (.use op), span⟩) m =
        ({ stack := ⟨#[tf₁]⟩, machine := mach₃ }, .ok ()) := by
      rw [hm_pre]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hm_ok', hcopy_imm]
      simp only [bind, EStateM.bind, annealReadImmediateLM2_2, pure, EStateM.pure]
      rw [hw]
    have htf₁_loc : tf₁.location = topFrame.location := by rw [htf₁]; rfl
    have htf₁_body : tf₁.body = topFrame.body := by rw [htf₁]; rfl
    have htf₁_rc : tf₁.returnContinuation = topFrame.returnContinuation := by rw [htf₁]; rfl
    have htf₁_rp : tf₁.returnPlace = topFrame.returnPlace := by rw [htf₁]; rfl
    have htf₁_id : tf₁.localsIdentity = topFrame.localsIdentity := by rw [htf₁]; rfl
    have hloc₁ : tf₁.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
      rw [htf₁_loc]; exact hframe.location_eq
    have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
      hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl hloc₁
    -- Anneal: field `f` of the union value becomes `sc'`.
    have hvld := (WellTypedLM2_1ScalarOperand.ofScalar hop_tf).validateLoadedValue_true hbool'
    have hrv : evalRvalue s.frame.locals (.use op) s.memory body.localDecls body.layouts =
        .ok (.scalar sc') s.frame.locals s.memory := by
      unfold evalRvalue; dsimp only; rw [hbor, hcaller, hop_ld, ha_ok]; dsimp only; rw [hvld]
      simp only []
    have hwp := writeProjectedForLocal_union_field_ge (locals := s.frame.locals) hdecl_u hwt
      hfields hf hf hprim0 himm0 hfl hprim0 himm' (Nat.le_of_eq hk'.symm) (hk' ▸ hk_le0) hfl
    let locals₂ := s.frame.locals.set u (.init (.aggregate 0 (unionSlotFields n f (.scalar sc'))))
    have ha_ok' : evalStmt s ⟨.assign ⟨u, [.field f f0Ty]⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.step (advanceStmt s locals₂ s.memory) := by
      unfold evalStmt; dsimp only; rw [hrv]; simp only []
      rw [hu_slot]; dsimp only
      rw [hwp]; dsimp only
      rw [set?_eq_some_set hlt_af_u, hprot, hbor]
      dsimp only [invalidateConflictingBorrowsAtProj]
      rw [hmem_same]
    -- The post-state relation.
    have hu₀ : topFrame₀.locals[u]? = some ⟨.live (.indirect mp), some layU⟩ := by
      dsimp only [topFrame₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set_self]
      simp [hmls_u_eq]
    have hu₁ : tf₁.locals[u]? = some ⟨.live (.indirect mp), some layU⟩ := by
      rw [hind₁ u mp (some layU) hu₀, hu₀]
    have hdisj₁' := hdisj₁ hdisj₀
    let tf_fin := { tf₁ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
    let m' : AnnealStepState := { stack := ⟨#[tf_fin]⟩, machine := mach₃ }
    have hframe_fin : FrameRelLM2_4 body mach₃ (advanceStmt s locals₂ s.memory).frame tf_fin :=
      { body_eq := by show tf₁.body = _; rw [htf₁_body]; exact hframe.body_eq
        location_eq := rfl
        af_locals_len := by
          show (s.frame.locals.set u _).length = _
          rw [List.length_set]
          exact hframe.af_locals_len
        mf_locals_size := hframe₁.mf_locals_size
        locals_rel := by
          intro i decl slot mls hdecl hslot hmls
          have hslot' : get? locals₂ i = some slot := hslot
          have hmls' : tf₁.locals[i]? = some mls := hmls
          rw [get?_eq_getElem?, List.getElem?_set] at hslot'
          by_cases hiu : u = i
          · subst hiu
            simp only [↓reduceIte, hlt_af_u, Option.some.injEq] at hslot'
            subst hslot'
            rw [hu₁] at hmls'; injection hmls' with hmls'; subst hmls'
            rw [hdecl_u] at hdecl; cases hdecl
            exact .union S n f f0Ty sc' mp _ (fun l hl => (Option.some.inj hl).symm) hwt hfields
              hf hmem'
          · simp only [hiu, ↓reduceIte] at hslot'
            have hloc := hframe₁.locals_rel i decl slot mls hdecl hslot' hmls'
            refine hloc.of_entry ?_
            intro mp_i c_i hmi a la hpa hla
            subst hmi
            have hne_a : a ≠ allocId := by
              intro hae; subst hae
              have := hdisj₁' u i mp mp_i (some layU) c_i hiu hu₁ hmls'
              rw [hprov_a, hpa] at this
              exact this rfl
            exact ⟨hother a la hne_a hla, rfl⟩ }
    have hstate' : StateRelLM2_4 body (advanceStmt s locals₂ s.memory) m' :=
      StateRelLM2_4.mk tf_fin rfl (by show tf₁.returnContinuation = _; rw [htf₁_rc]; exact hretCont)
        ⟨retLay, by
          show tf₁.returnPlace = .frameLocal 0 0 none retLay tf₁.localsIdentity
          rw [htf₁_rp, htf₁_id]
          exact hretPlace⟩
        hframe_fin hcal hstack hbor hprot hcaller hdisj₁'
    rw [hstep_a, ha_ok', hstep_m]
    refine ⟨.step _ _ hstate', fun s'' hs'' => ?_⟩
    have hs''' := MirStepNode_step_inj hs''
    subst hs'''
    refine ⟨sc', m', tf_fin, rfl, ha_ok, hstate', ?_, ?_, rfl, ⟨some layU, hu₁⟩, hmem', hnodup',
      ?_, rfl, rfl, ?_⟩
    · simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_u]
    · intro j hj
      simp [advanceStmt, locals₂, get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hj)]
    · intro tf htf j himm_j
      rw [hframes] at htf
      have htf' : topFrame = tf := by simpa using htf
      subst htf'
      exact hmono₁ j (himm_j.cache_layout hlt_u layU)
    · intro _ hw0 _
      obtain ⟨hw', hnext⟩ := MemoryHighWater.inplaceMachine (kind := kind) (alloc := A')
        (allocIdx := allocIdx) hw0 hlive₀
      exact ⟨hw', by rw [hnext]; omega⟩

/-- `annealEvalUnionFieldPlace` on an uninitialized immediate union local: the
local moves into the fresh allocation `id` (the vendored `forceAllocation`), and
the field's place is that allocation's place, at offset `0`. -/
theorem annealEvalUnionFieldPlace_uninit
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {u : Nat} {uDecl : LocalDecl} (hlt : u < tf.locals.size)
    (hdecl : get? body.localDecls u = some uDecl)
    (hcache : ∀ l, (tf.locals[u]'hlt).layout = some l → l = translateTy uDecl.ty body.layouts)
    (hval : (tf.locals[u]'hlt).value = .live (.immediate .uninit))
    {n j : Nat} (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hj : j < n) (hsized : (translateTy uDecl.ty body.layouts).layout.isSized = true)
    {fty : Ty} (hprim : IsPrimScalarTy fty)
    {alloc : Miri.Memory.Allocation AnnealProv Unit}
    (htry : Miri.Memory.Allocation.tryNew (translateTy uDecl.ty body.layouts).layout.size
      (translateTy uDecl.ty body.layouts).layout.align.abi .Uninit annealZeroedStorage = .ok alloc)
    {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id))
    (hlt₀ : u < (cacheFrameLocalLayout tf u hlt (translateTy uDecl.ty body.layouts)).locals.size) :
    annealEvalUnionFieldPlace body.localDecls body.layouts u j (encodeTyId fty) m =
      .ok ⟨.memory (stackAllocPlace id), translateTy fty body.layouts⟩
        { stack := ⟨#[setFrameLocalIndirect
            (cacheFrameLocalLayout tf u hlt (translateTy uDecl.ty body.layouts)) u hlt₀
            (stackAllocPlace id)]⟩,
          machine := stackAllocMachine m.machine mem' id (alloc.withExtra none) } := by
  have hres_c := annealResolveAndCacheLocalLayout_eq (known := none) hframes hlt hdecl hcache
  let tf₀ := cacheFrameLocalLayout tf u hlt (translateTy uDecl.ty body.layouts)
  have hgo : tf₀.getLocalOperand u = .ok (.immediate .uninit) := by
    apply frame_getLocalOperand_live
    rw [cacheFrameLocalLayout_getLocal]
    rw [← hval]
  have hc₀ : (tf₀.locals[u]'hlt₀).layout = some (translateTy uDecl.ty body.layouts) := by
    simp [tf₀, cacheFrameLocalLayout]
  have hval₀ : (tf₀.locals[u]'hlt₀).value = .live (.immediate .uninit) := by
    simp [tf₀, cacheFrameLocalLayout, hval]
  have hcf := cacheFrameLocalLayout_of_cached tf₀ hlt₀ hc₀
  have hlt₀' : u < (cacheFrameLocalLayout tf₀ u hlt₀
      (translateTy uDecl.ty body.layouts)).locals.size := by
    rw [hcf]; exact hlt₀
  have hforce := forceAllocation_uninit_eq (body := body) (m := { m with stack := ⟨#[tf₀]⟩ }) rfl
    hlt₀ hdecl (fun l hl => by rw [hc₀] at hl; exact (Option.some.inj hl).symm) hval₀ hsized htry
    hres tf₀.localsIdentity (translateTy uDecl.ty body.layouts) hlt₀'
  rw [setFrameLocalIndirect_congr hcf hlt₀' hlt₀] at hforce
  have hproj := projectField_union (setFrameLocalIndirect tf₀ u hlt₀ (stackAllocPlace id))
    body.layouts (stackAllocMachine m.machine mem' id (alloc.withExtra none)) hfields hj hprim
    (mp := stackAllocPlace id) rfl
  have hsize : m.stack.frames.size - 1 = 0 := by rw [hframes]; rfl
  dsimp only [tf₀] at hgo hforce hproj
  unfold annealEvalUnionFieldPlace
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton m.stack tf hframes, Option.isNone_some,
    Bool.false_eq_true, ↓reduceIte, hres_c, hgo, hsize, pure]
  simp only [hforce, EStateM.pure, stack_currentFrame?_singleton _
    (setFrameLocalIndirect (cacheFrameLocalLayout tf u hlt (translateTy uDecl.ty body.layouts)) u
      hlt₀ (stackAllocPlace id)) rfl, hproj]

/-- **`step_union_field_write_uninit_simulation`** (`D13b` upgrade of
`step_union_field_write_uninit_divergence`): the projected write `_u.j = op`
(`j < n`, `WellTypedScalarOperand`) into an uninitialized union local `_u`
(MIR that borrowck rejects in surface Rust, yet `core::intrinsics::mir` can
express).

Both machines step in lockstep (`StepRelLM2_4`):
1. If `op` reads a dead or uninitialized local, both machines report undefined
   behavior (`StepRelLM2_4.ub`).
2. Otherwise `op` evaluates to `.scalar sc`, Anneal materializes the union shell
   via `uninitFieldWriteShell?` + `writeProjectedForLocal` to store
   `.init (.aggregate 0 (unionSlotFields n j (.scalar sc)))`, and `lean-miri`
   moves `_u` into a fresh stack allocation (`forceAllocation`), writes `sc`
   into its bytes `[0, k)`, and leaves `[k, S)` uninitialized (`UnionMemRel`,
   preserving `StateRelLM2_4`, `LiveAllocsNodup`, and `StepPreservesHighWater m 1`). -/
theorem step_union_field_write_uninit_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {u j : Local} {fty : Ty} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩)
    {uDecl : LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {S n : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hj : j < n)
    (hu_uninit : get? s.frame.locals u = some .uninit)
    (hu_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame u)
    (hprim : IsPrimScalarTy fty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op fty)
    (hf_le : (translateTy fty body.layouts).layout.size.bytes.toNat ≤ S)
    (hfl : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) j = some fl ∧
      fl.layout.size = (translateTy fty body.layouts).layout.size := by exact ⟨_, rfl, rfl⟩) :
    StepRelLM2_4 body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      ∃ (sc : MirAst.ScalarInt) (mp : Miri.Interpreter.MemPlace AnnealProv)
        (m' : AnnealStepState)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
          .ok (.scalar sc) s.frame.locals ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals u =
          some (.init (.aggregate 0 (unionSlotFields n j (.scalar sc)))) ∧
        (∀ k, k ≠ u → get? s'.frame.locals k = get? s.frame.locals k) ∧
        m'.stack.frames = #[tf'] ∧
        (∃ c', tf'.locals[u]? = some ⟨.live (.indirect mp), c'⟩) ∧
        UnionMemRel m'.machine uDecl.ty body.layouts S fty sc mp ∧
        LiveAllocsNodup m'.machine ∧
        (∀ tf, m.stack.frames = #[tf] → ∀ k, k ≠ u →
          IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) ∧
        s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
        StepPreservesHighWater m 1 (m', .ok true)) := by
  rcases hstate with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  obtain ⟨mem', id, hres⟩ := hcanRes
  have hop_tf := hop topFrame hframes
  have hop_ld := hop_tf.evalOperand_localDecls_eq s.frame.locals s.memory.globals
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem; dsimp only at hbor hprot; subst hbor hprot; rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩ body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
  obtain ⟨slot_u, mls_u, hlt_af_u, hlt_u, hslot_u, hmls_u, hmls_u_eq, hloc_u⟩ :=
    hframe.lookup_local hdecl_u
  rw [hu_uninit] at hslot_u; injection hslot_u with hslot_u; subst hslot_u
  have hu_imm' := hu_imm topFrame hframes mls_u hmls_u
  have hloc_u' : LocalRel m.machine uDecl body.layouts .uninit mls_u := by
    cases hloc_u with | base _ _ hl => exact hl
  have hcache_u := hloc_u'.layout_eq
  have hmls_u_val : mls_u.value = .live (.immediate .uninit) := by
    cases hloc_u' with
    | indirect _ mp' _ _ _ _ => exact absurd rfl (hu_imm' mp')
    | immediate _ imm _ _ hv =>
      rcases hv with ⟨_, rfl⟩ | ⟨_, h, _⟩
      · rfl
      · cases h
  have hS := hwt.size_valid
  have hS16 : S ≤ 16 := by rcases hS with h | h | h | h | h <;> omega
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame u hlt_u layU
  obtain ⟨alloc, htry, hbs, hlen, hnat, hmut, hal, hprov, hmask⟩ :=
    freshUnionAlloc_spec layU.layout.size layU.layout.align.abi (translateTy_align_pow2_le_29 _ _)
  have hlt₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hplace := annealEvalUnionFieldPlace_uninit (body := body) hframes hlt_u hdecl_u
    (by rw [hmls_u_eq]; exact hcache_u) (by rw [hmls_u_eq]; exact hmls_u_val) hfields hj
    hwt.sized hprim htry hres hlt₀
  let mp := stackAllocPlace id
  let tf₁ := setFrameLocalIndirect topFrame₀ u hlt₀ mp
  let mach₁ := stackAllocMachine m.machine mem' id (alloc.withExtra none)
  let st₁ : AnnealStepState := { stack := ⟨#[tf₁]⟩, machine := mach₁ }
  let dest : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.memory mp, translateTy fty body.layouts⟩
  have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
  have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
      ⟨u, #[.Field j (encodeTyId fty)]⟩ true m = .ok dest st₁ := by
    show annealEvalPlaceLM2_4 body.localDecls body.layouts ⟨u, #[.Field j (encodeTyId fty)]⟩ m = _
    simp only [annealEvalPlaceLM2_4, hunion, ↓reduceIte]
    exact hplace
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨u, #[.Field j (encodeTyId fty)]⟩
      (translateRvalue (.use op)) = true := by
    simp [lm24Assign, lm24Place, hunion]
  have hm_pre : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
          (some (translateTy fty body.layouts)) >>= fun o =>
          (annealRvalueHooksLM2_4 body.localDecls body.layouts).copyOp () o dest) st₁ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateProjectionElem]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace']
    dsimp only [translateRvalue]
    rfl
  have hcopy_imm : ∀ (imm : Miri.Interpreter.Immediate AnnealProv)
      (lay : Miri.Interpreter.LocalLayout) (st : AnnealStepState),
      (annealRvalueHooksLM2_4 body.localDecls body.layouts).copyOp () ⟨.immediate imm, lay⟩ dest st =
        (annealReadImmediateLM2_2 ⟨.immediate imm, lay⟩ >>= fun i => annealWriteImmediateLM2_2 i.imm dest) st := by
    intro imm lay st; rfl
  have hframe₀ : FrameRelLM2_4 body m.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_u hlt_u
  have hop₀ : WellTypedScalarOperand body topFrame₀ op fty := hop_tf.cache_layout hlt_u layU
  have hne : ∀ idx, op = .copy ⟨idx, .nil⟩ → idx ≠ u := by
    intro idx hidx; subst hidx
    cases hop_tf with
    | copyLocal _ decl hdecl _ _ => exact primScalar_ne_union_local hdecl_u hwt hdecl hprim
  have hagg_op_eq : ∀ st,
      (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
        (.rvalue "operand") (translateOperand op) (some (translateTy fty body.layouts)) st =
      (annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        (some (translateTy fty body.layouts)) >>= fun o => do
          let imm ← annealReadImmediateLM2_2 o
          return (⟨.immediate imm.imm, imm.layout⟩ : Miri.Interpreter.OpTy AnnealProv)) st :=
    fun _ => rfl
  rcases evalScalarOperand_union_dst (mach' := mach₁) hframe₀ hprim hop₀ hne hlt₀ mp
      s.memory.globals (.rvalue "operand") (some (translateTy fty body.layouts)) with
    ⟨ha_ub, m_err, msg, hm_err⟩ |
    ⟨sc, msc, tf₂, hlt₂, ha_ok, hm_ok, hframe₂, hdisj₂, hmono₂, htf₂, _, hrel, himmRel⟩
  · -- `op` reads a dead or uninitialized local: UB in both machines.
    have ha : evalStmt s ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue; dsimp only; rw [hbor, hcaller, hop_ld, ha_ub]
    have hm_err_bind : (annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        (some (translateTy fty body.layouts)) >>= fun o =>
        (annealRvalueHooksLM2_4 body.localDecls body.layouts).copyOp () o dest) st₁ =
        .error (.undefinedBehavior msg) m_err := by
      rw [hagg_op_eq] at hm_err
      cases hop_st : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
          (some (translateTy fty body.layouts)) st₁ with
      | error e s_e =>
        rw [EStateM.bind_eq_error hop_st]
        rw [EStateM.bind_eq_error hop_st] at hm_err
        injection hm_err with he hs; subst he hs; rfl
      | ok o s_o =>
        have ho_imm : ∃ imm lay, o = ⟨.immediate imm, lay⟩ := by
          have hop_lm : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
              (some (translateTy fty body.layouts)) st₁ =
              annealEvalOperand body.localDecls body.layouts (translateOperand op)
                (some (translateTy fty body.layouts)) st₁ := by
            cases hop_tf <;> rfl
          rw [hop_lm] at hop_st
          cases hop_tf with
          | constScalar c _ hval hp_c hsz_c hcan_c _ _ _ =>
            obtain ⟨msc_c, htry_c, _⟩ := tryFromUInt_of_valid_canonical hsz_c hcan_c
            have hev_c : annealEvalOperand body.localDecls body.layouts
                (translateOperand (.constant c)) (some (translateTy c.ty body.layouts)) st₁ =
                .ok ⟨.immediate (.scalar (.fromScalarInt msc_c)), translateTy c.ty body.layouts⟩ st₁ := by
              with_unfolding_all
                unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
                dsimp only; rw [hval]
                simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
                  EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
                  stack_currentFrame?_singleton st₁.stack tf₁ rfl, Option.isNone_some,
                  Bool.false_eq_true, ↓reduceIte, htry_c, hp_c.layoutOfEncoded]
            rw [hev_c] at hop_st; cases hop_st; exact ⟨_, _, rfl⟩
          | copyLocal idx decl hdecl _ himm_idx =>
            have hne_iu : idx ≠ u := hne idx rfl
            obtain ⟨_, mls_i, _, hlt_i, _, hmls_i, _, hloc_i⟩ := hframe₀.lookup_local hdecl
            have hlt_i1 : idx < tf₁.locals.size := by
              dsimp only [tf₁, setFrameLocalIndirect]; rw [Array.size_set]; exact hlt_i
            have hmls_i1 : tf₁.locals[idx]'hlt_i1 = mls_i :=
              Option.some.inj (by
                rw [← Array.getElem?_eq_getElem]
                dsimp only [tf₁, setFrameLocalIndirect]
                rw [Array.getElem?_set_ne _ hne_iu.symm]; exact hmls_i)
            have himm_i := (himm_idx.cache_layout hlt_u layU) mls_i hmls_i
            cases hloc_i with
            | union _ _ _ _ _ mp' _ _ _ _ _ _ => exact absurd rfl (himm_i mp')
            | base _ _ hl_i =>
              cases hl_i with
              | dead _ hcache_i =>
                have hd := annealEvalOperand_copy_dead (m := st₁) (topFrame := tf₁)
                  (known := some (translateTy decl.ty body.layouts)) rfl hlt_i1 hdecl hmls_i1 hcache_i
                dsimp only [translateOperand, translatePlace, List.map, List.toArray] at hop_st
                rw [hd] at hop_st; cases hop_st
              | indirect _ mp' _ _ _ _ => exact absurd rfl (himm_i mp')
              | immediate _ imm_i _ hcache_i _ =>
                have hl := annealEvalOperand_copy_live (m := st₁) (topFrame := tf₁)
                  (known := some (translateTy decl.ty body.layouts)) rfl hlt_i1 hdecl hmls_i1 hcache_i
                dsimp only [translateOperand, translatePlace, List.map, List.toArray] at hop_st
                rw [hl] at hop_st; cases hop_st; exact ⟨_, _, rfl⟩
        obtain ⟨imm, lay, rfl⟩ := ho_imm
        rw [EStateM.bind_eq_ok hop_st, hcopy_imm]
        rw [EStateM.bind_eq_ok hop_st] at hm_err
        cases hr : annealReadImmediateLM2_2 ⟨.immediate imm, lay⟩ s_o with
        | error e' s' =>
          rw [EStateM.bind_eq_error hr]
          rw [EStateM.bind_eq_error hr] at hm_err
          injection hm_err with he hs; subst he hs; rfl
        | ok iv s' =>
          rw [EStateM.bind_eq_ok hr] at hm_err
          cases hm_err
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩) m =
        (m_err, .error (.undefinedBehavior msg)) := by
      rw [hm_pre]; unfold Miri.Interpreter.runRvalue; rw [hm_err_bind]
    rw [hstep_a, ha, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_stmt]
    exact ⟨.ub _ _, fun _ h => absurd h MirStepNode_fail_ne_step⟩
  · -- `op` evaluates to `sc`: write `sc` into `[0, k)` of the fresh allocation.
    cases himmRel with
    | scalar _ _ hrel_imm hsz_k hbool_sc hchar_sc =>
    have himmRel : ImmediateRel fty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)) :=
      .scalar sc msc hrel_imm hsz_k hbool_sc hchar_sc
    have hkv : ValidScalarBytes sc.sizeBytes := hrel.validBytes
    have hk_le : sc.sizeBytes ≤ S := by
      have h := translateSizeBytes_toNat_of_valid hkv
      rw [hsz_k, h] at hf_le; exact hf_le
    have hlay_sz : layU.layout.size = translateSizeBytes S := hwt.size_eq
    have hA_len : (alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).len = S := by
      show alloc.len = S; rw [hlen, hlay_sz]; exact translateSizeBytes_toNat_of_valid hS
    have hA_sz : (alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).byteSize =
        translateSizeBytes S := by
      show alloc.byteSize = _; rw [hbs, hlay_sz]
    have hset : (alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).initializationMask.setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) true =
        .ok (unionPrefixMask S sc.sizeBytes) := by
      show alloc.initializationMask.setRange _ true = _
      rw [hmask, hlay_sz]; exact unionPrefixMask_fresh hS hkv hk_le
    have hfresh : mem'.live.any (fun entry => entry.1 == id) = false := by
      have h := (reserveAllocId_ok_live hres).2
      rwa [← (reserveAllocId_ok_live hres).1] at h
    let tf₃ := setFrameLocalIndirect tf₂ u hlt₂ mp
    obtain ⟨A', hw, hA'_sz, hA'_len, hA'_align, hA'_mut, hA'_prov, hA'_mask, hA'_extra,
        hA'_native, hA'_raw⟩ :=
      annealWriteImmediate_unionFresh (mach := m.machine) (tf := tf₃)
        (destLay := translateTy fty body.layouts) hfresh hrel hA_len hA_sz hS16 hk_le hmut hprov
        hset
    let mach₃ := stackAllocMachine m.machine mem' id A'
    let st₃ : AnnealStepState := { stack := ⟨#[tf₃]⟩, machine := mach₃ }
    have hop_st_ok : (annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        (some (translateTy fty body.layouts)) >>= fun o =>
        (annealRvalueHooksLM2_4 body.localDecls body.layouts).copyOp () o dest) st₁ =
        .ok () st₃ := by
      rw [hagg_op_eq] at hm_ok
      cases hop_st : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
          (some (translateTy fty body.layouts)) st₁ with
      | error _ _ => rw [EStateM.bind_eq_error hop_st] at hm_ok; cases hm_ok
      | ok o s_o =>
        have ho_imm : ∃ imm lay, o = ⟨.immediate imm, lay⟩ := by
          have hop_lm : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
              (some (translateTy fty body.layouts)) st₁ =
              annealEvalOperand body.localDecls body.layouts (translateOperand op)
                (some (translateTy fty body.layouts)) st₁ := by
            cases hop_tf <;> rfl
          rw [hop_lm] at hop_st
          cases hop_tf with
          | constScalar c _ hval hp_c hsz_c hcan_c _ _ _ =>
            obtain ⟨msc_c, htry_c, _⟩ := tryFromUInt_of_valid_canonical hsz_c hcan_c
            have hev_c : annealEvalOperand body.localDecls body.layouts
                (translateOperand (.constant c)) (some (translateTy c.ty body.layouts)) st₁ =
                .ok ⟨.immediate (.scalar (.fromScalarInt msc_c)), translateTy c.ty body.layouts⟩ st₁ := by
              with_unfolding_all
                unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
                dsimp only; rw [hval]
                simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
                  EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
                  stack_currentFrame?_singleton st₁.stack tf₁ rfl, Option.isNone_some,
                  Bool.false_eq_true, ↓reduceIte, htry_c, hp_c.layoutOfEncoded]
            rw [hev_c] at hop_st; cases hop_st; exact ⟨_, _, rfl⟩
          | copyLocal idx decl hdecl _ himm_idx =>
            have hne_iu : idx ≠ u := hne idx rfl
            obtain ⟨_, mls_i, _, hlt_i, _, hmls_i, _, hloc_i⟩ := hframe₀.lookup_local hdecl
            have hlt_i1 : idx < tf₁.locals.size := by
              dsimp only [tf₁, setFrameLocalIndirect]; rw [Array.size_set]; exact hlt_i
            have hmls_i1 : tf₁.locals[idx]'hlt_i1 = mls_i :=
              Option.some.inj (by
                rw [← Array.getElem?_eq_getElem]
                dsimp only [tf₁, setFrameLocalIndirect]
                rw [Array.getElem?_set_ne _ hne_iu.symm]; exact hmls_i)
            have himm_i := (himm_idx.cache_layout hlt_u layU) mls_i hmls_i
            cases hloc_i with
            | union _ _ _ _ _ mp' _ _ _ _ _ _ => exact absurd rfl (himm_i mp')
            | base _ _ hl_i =>
              cases hl_i with
              | dead _ hcache_i =>
                have hd := annealEvalOperand_copy_dead (m := st₁) (topFrame := tf₁)
                  (known := some (translateTy decl.ty body.layouts)) rfl hlt_i1 hdecl hmls_i1 hcache_i
                dsimp only [translateOperand, translatePlace, List.map, List.toArray] at hop_st
                rw [hd] at hop_st; cases hop_st
              | indirect _ mp' _ _ _ _ => exact absurd rfl (himm_i mp')
              | immediate _ imm_i _ hcache_i _ =>
                have hl := annealEvalOperand_copy_live (m := st₁) (topFrame := tf₁)
                  (known := some (translateTy decl.ty body.layouts)) rfl hlt_i1 hdecl hmls_i1 hcache_i
                dsimp only [translateOperand, translatePlace, List.map, List.toArray] at hop_st
                rw [hl] at hop_st; cases hop_st; exact ⟨_, _, rfl⟩
        obtain ⟨imm, lay, rfl⟩ := ho_imm
        rw [EStateM.bind_eq_ok hop_st] at hm_ok
        cases hr : annealReadImmediateLM2_2 ⟨.immediate imm, lay⟩ s_o with
        | error _ _ => rw [EStateM.bind_eq_error hr] at hm_ok; cases hm_ok
        | ok iv s' =>
          rw [EStateM.bind_eq_ok hr] at hm_ok
          dsimp only [pure, EStateM.pure] at hm_ok
          injection hm_ok with hop_v hs'
          injection hop_v with himm_eq _
          injection himm_eq with himm_eq
          rw [EStateM.bind_eq_ok hop_st, hcopy_imm, EStateM.bind_eq_ok hr, himm_eq, hs']
          exact hw
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩) m =
        (st₃, .ok ()) := by
      rw [hm_pre]; unfold Miri.Interpreter.runRvalue; rw [hop_st_ok]
    have hloc₃ : tf₃.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
      show tf₂.location = _
      have h : tf₂.location = topFrame₀.location := by rw [htf₂]
      rw [h]; exact hframe.location_eq
    have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
      hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl hloc₃
    -- Anneal: `uninitFieldWriteShell?` + `writeProjectedForLocal` initializes `_u`.
    have hvld := (WellTypedLM2_1ScalarOperand.ofScalar hop_tf).validateLoadedValue_true hbool_sc
    have hrv : evalRvalue s.frame.locals (.use op) s.memory body.localDecls body.layouts =
        .ok (.scalar sc) s.frame.locals s.memory := by
      unfold evalRvalue; dsimp only; rw [hbor, hcaller, hop_ld, ha_ok]; dsimp only; rw [hvld]
      simp only []
    obtain ⟨hshell, hwp⟩ := writeProjectedForLocal_union_field_uninit (locals := s.frame.locals)
      hdecl_u hwt hfields hj hprim himmRel hk_le hfl
    let locals₂ := s.frame.locals.set u (.init (.aggregate 0 (unionSlotFields n j (.scalar sc))))
    have ha_ok' : evalStmt s ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.step (advanceStmt s locals₂ s.memory) := by
      unfold evalStmt; dsimp only; rw [hrv]; simp only []
      rw [hu_uninit]; dsimp only
      rw [hshell]; dsimp only
      rw [hwp]; dsimp only
      rw [set?_eq_some_set hlt_af_u, hprot, hbor]
      dsimp only [invalidateConflictingBorrowsAtProj]
      rw [hmem_same]
    -- Post-state relation.
    let tf_fin := { tf₃ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
    let m' : AnnealStepState := { st₃ with stack := ⟨#[tf_fin]⟩ }
    have hmem_rel : UnionMemRel mach₃ uDecl.ty body.layouts S fty sc mp :=
      .mk id .one (annealStackBaseAddr id) ⟨.stack, A'⟩ msc rfl rfl rfl
        (by simp [mach₃, stackAllocMachine])
        (lookupBaseAddr_stackAllocMachine_self _ _ _ _) rfl (annealStackBaseAddr_add_lt id hS16)
        (hA'_sz.trans hA_sz) hA'_len hA'_mut hA'_prov (hA'_align.trans hal) hA'_extra
        (hA'_native.trans hnat) hk_le (hA'_mask ▸ .of_fresh S sc.sizeBytes) hrel hprim himmRel hA'_raw
    have htf₂_body : tf₂.body = topFrame.body := by rw [htf₂]; rfl
    have htf₂_rc : tf₂.returnContinuation = topFrame.returnContinuation := by rw [htf₂]; rfl
    have htf₂_rp : tf₂.returnPlace = topFrame.returnPlace := by rw [htf₂]; rfl
    have htf₂_id : tf₂.localsIdentity = topFrame.localsIdentity := by rw [htf₂]; rfl
    obtain ⟨hlive_b, hfreshne, hbase_b⟩ := stackAllocMachine_live_base (mach := m.machine) A' hres
    have hframe_fin : FrameRelLM2_4 body mach₃ (advanceStmt s locals₂ s.memory).frame tf_fin :=
      { body_eq := by show tf₂.body = _; rw [htf₂_body]; exact hframe.body_eq
        location_eq := rfl
        af_locals_len := by
          show (s.frame.locals.set u _).length = _
          rw [List.length_set]; exact hframe.af_locals_len
        mf_locals_size := by
          show (tf₂.locals.set u _ hlt₂).size = _
          rw [Array.size_set]; exact hframe₂.mf_locals_size
        locals_rel := by
          intro i decl slot mls hdecl hslot hmls
          have hslot' : get? locals₂ i = some slot := hslot
          have hmls' : (tf₂.locals.set u
              { tf₂.locals[u]'hlt₂ with value := .live (.indirect mp) } hlt₂)[i]? = some mls := hmls
          rw [get?_eq_getElem?, List.getElem?_set] at hslot'
          rw [Array.getElem?_set] at hmls'
          by_cases hiu : u = i
          · subst hiu
            simp only [↓reduceIte, hlt_af_u, Option.some.injEq] at hslot' hmls'
            subst hslot' hmls'
            rw [hdecl_u] at hdecl; cases hdecl
            have hloc₂ := hframe₂.locals_rel u uDecl .uninit (tf₂.locals[u]'hlt₂) hdecl_u
              hu_uninit (Array.getElem?_eq_getElem hlt₂)
            exact .union S n j fty sc mp _ hloc₂.layout_eq hwt hfields hj hmem_rel
          · simp only [hiu, ↓reduceIte] at hslot' hmls'
            exact (hframe₂.locals_rel i decl slot mls hdecl hslot' hmls').of_live_base
              hlive_b hbase_b }
    have hdisj_fin : MemoryAllocDisjoint tf_fin := by
      have hdisj₂' : MemoryAllocDisjoint tf₂ := hdisj₂ (hdisj.cache_layout hlt_u layU)
      intro i k mp_i mp_k lay_i lay_k hik hi hk
      dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hi hk
      rw [Array.getElem?_set] at hi hk
      by_cases hi_u : u = i
      · subst hi_u
        have hk_u : u ≠ k := hik
        simp only [hk_u, ↓reduceIte] at hk
        simp only [↓reduceIte] at hi
        obtain ⟨a, la, ha, hla⟩ := hframe₂.indirect_allocId hk
        injection hi with hi; injection hi with hv _; injection hv with hv; injection hv with hv
        subst hv; rw [ha]
        simp only [mp, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
          Option.some.injEq]
        exact fun h => hfreshne a la hla h.symm
      · simp only [hi_u, ↓reduceIte] at hi
        by_cases hk_u : u = k
        · subst hk_u
          simp only [↓reduceIte] at hk
          obtain ⟨a, la, ha, hla⟩ := hframe₂.indirect_allocId hi
          injection hk with hk; injection hk with hv _; injection hv with hv; injection hv with hv
          subst hv; rw [ha]
          simp only [mp, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
            Option.some.injEq]
          exact hfreshne a la hla
        · simp only [hk_u, ↓reduceIte] at hk
          exact hdisj₂' i k mp_i mp_k lay_i lay_k hik hi hk
    have hstate' : StateRelLM2_4 body (advanceStmt s locals₂ s.memory) m' :=
      StateRelLM2_4.mk tf_fin rfl (by show tf₂.returnContinuation = _; rw [htf₂_rc]; exact hretCont)
        ⟨retLay, by show tf₂.returnPlace = .frameLocal 0 0 none retLay tf₂.localsIdentity
                    rw [htf₂_rp, htf₂_id]; exact hretPlace⟩
        hframe_fin hcal hstack hbor hprot hcaller hdisj_fin
    have himm_fin : ∀ tf, m.stack.frames = #[tf] → ∀ k, k ≠ u →
        IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf_fin k := by
      intro tf htf k hk himm_k
      rw [hframes] at htf
      have htf' : topFrame = tf := by simpa using htf
      subst htf'
      have h₂ := hmono₂ k (himm_k.cache_layout hlt_u layU)
      intro mls hmls
      dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hmls
      rw [Array.getElem?_set_ne _ (Ne.symm hk)] at hmls
      exact h₂ mls hmls
    rw [hstep_a, ha_ok', hstep_m]
    refine ⟨.step _ _ hstate', fun s' hs' => ?_⟩
    have hs'' := MirStepNode_step_inj hs'
    subst hs''
    refine ⟨sc, mp, m', tf_fin, rfl, ha_ok, hstate', ?_, ?_, rfl,
      ⟨(tf₂.locals[u]'hlt₂).layout, ?_⟩, hmem_rel, LiveAllocsNodup.stackAllocMachine A' hnodup hres,
      himm_fin, rfl, rfl, fun _ hw hb => MemoryHighWater.stackAllocMachine A' hw hb hres⟩
    · simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_u]
    · intro k hk
      simp [advanceStmt, locals₂, get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hk)]
    · simp [tf_fin, tf₃, setFrameLocalIndirect]

/-! ## 12. `Subslice` Operands (`evalSubsliceOperand_simulation`)

`annealEvalOperandLM2_4` sends an operand whose projection contains a
`Subslice` to `annealEvalSubsliceOperand`, which checks that the whole array is
initialized before projecting. The theorems below lift
`evalProjection_subslice_simulation` from projections to these operands. -/

/-- A memory-backed array of `count > 0` elements that Anneal holds as
`.uninit` fails `annealCheckIndirectInitialized`. -/
theorem annealCheckIndirectInitialized_uninit_array_ub
    {mach : AnnealMachine} {layouts : LayoutTable}
    {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup mach)
    (hmp : MemPlaceRel mach arrTy layouts none mp) (hpos : 0 < count) :
    annealCheckIndirectInitialized mach mp (translateTy arrTy layouts).layout.size =
      .error (.undefinedBehavior "access to uninitialized indirect place") := by
  cases hmp with
  | mk allocId tag baseAddr relOffset localAlloc
      hprov _ _ hlive hbase _ hptr _ _ _ huninit_cons _ _ _ =>
    have hfind := array_find?_of_nodup_fst hnodup hlive
    have hrel_sz : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = relOffset := by
      have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
      rw [hbytes, uint64_add_sub_cancel_left]; cases relOffset; rfl
    have hsz_nz : (translateTy arrTy layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
      intro hzero
      have hbytes0 : (translateTy arrTy layouts).layout.size.bytes.toNat = 0 := by
        rw [hzero]; rfl
      rw [hwf.arr_size_toNat] at hbytes0
      have := Nat.mul_pos hpos hwf.elem_size_pos
      omega
    have hnot_init := huninit_cons rfl hsz_nz
    unfold annealCheckIndirectInitialized
    rw [hprov]
    simp only [Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind, hrel_sz]
    cases hmask : localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange relOffset (translateTy arrTy layouts).layout.size) with
    | error _ => rfl
    | ok inner =>
      cases inner with
      | error _ => rfl
      | ok u => cases u; exact absurd hmask hnot_init

/-- The operand `copy a[fromIdx..toIdx]` (`move a[fromIdx..toIdx]` when
`isMove`; `toIdx` counts from the end when `fromEnd`). -/
def subsliceReadOperand (isMove : Bool) (arrIdx : Local) (fromIdx toIdx : Nat)
    (fromEnd : Bool) : MirAst.Operand :=
  if isMove then .move ⟨arrIdx, [.subslice fromIdx toIdx fromEnd]⟩
  else .copy ⟨arrIdx, [.subslice fromIdx toIdx fromEnd]⟩

/-- `annealEvalOperandLM2_4` sends a `Subslice` operand, copied or moved, to
`annealEvalSubsliceOperand`. -/
theorem annealEvalOperandLM2_4_subslice (localDecls : List LocalDecl) (layouts : LayoutTable)
    (isMove : Bool) (arrIdx : Local) (fromIdx toIdx : Nat) (fromEnd : Bool)
    (known : Option Miri.Interpreter.LocalLayout) :
    annealEvalOperandLM2_4 localDecls layouts
        (translateOperand (subsliceReadOperand isMove arrIdx fromIdx toIdx fromEnd)) known =
      annealEvalSubsliceOperand localDecls layouts
        ⟨arrIdx, #[.Subslice fromIdx toIdx fromEnd]⟩ known := by
  cases isMove <;> rfl

/-- **`evalSubsliceOperand_simulation`** (`LM-2.4`): the operand
`copy a[fromIdx..toIdx]` (or `move a[fromIdx..toIdx]`) on an array local `a` of
`count` primitive scalars, evaluated by Anneal's `evalOperand` and by
`annealEvalOperandLM2_4` on `StateRelLM2_4`-related states.

1. A dead array, or an uninitialized one that `lean-miri` holds as an immediate
   or that has `0 < count` elements, is undefined behavior in both machines.
2. An initialized array is memory-backed at some `mp` (`MemPlaceRel`), and
   `lean-miri` caches `a`'s layout, leaving the states related, and finds the
   whole array initialized. In bounds (`SubsliceInBounds`), Anneal returns the
   sub-array of the elements `[fromIdx, end)` without changing any local, and
   `lean-miri` returns the place `fromIdx * elemSize` bytes further into that
   allocation, with layout `[T; end - fromIdx]`, whose bytes hold that
   sub-array (`ArraySliceRel`). A subslice counted from the end with
   `count < fromIdx + toIdx` is undefined behavior in both machines.

Both machines leave `a` initialized under `move`, as rustc does for projected
moves.

A memory-backed uninitialized array of `0` elements is characterized separately
by `evalSubsliceOperand_zero_uninit_indirect_characterization`: Anneal reports
undefined behavior for any read of an `.uninit` local, whereas `lean-miri`'s
`InitMask.isRangeInitialized` on `[off, off + 0)` rejects `.Lazy false` as
uninitialized (matching Anneal) and accepts `.Lazy true` or `.Materialized`. -/
theorem evalSubsliceOperand_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hstate : StateRelLM2_4 body s m)
    (hframes : m.stack.frames = #[topFrame])
    (hnodup : LiveAllocsNodup m.machine)
    {arrIdx : Local} {arrDecl : LocalDecl} {elemKind : RigidTy} {count : Nat}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (isMove : Bool) (fromIdx toIdx : Nat) (fromEnd : Bool)
    (known : Option Miri.Interpreter.LocalLayout) :
    let op := subsliceReadOperand isMove arrIdx fromIdx toIdx fromEnd
    let arrLay := translateTy arrDecl.ty body.layouts
    let es := (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size
    let cnt := subsliceEnd count toIdx fromEnd - fromIdx
    ((get? s.frame.locals arrIdx = some .dead ∨
        (get? s.frame.locals arrIdx = some .uninit ∧
          (0 < count ∨ IsImmediateFrameLocal topFrame arrIdx))) →
      evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil body.localDecls = .ub ∧
      ∃ m' msg, annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        known m = .error (.undefinedBehavior msg) m') ∧
    (∀ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)) →
      ∃ (mp : Miri.Interpreter.MemPlace AnnealProv)
        (topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        MemPlaceRel m.machine arrDecl.ty body.layouts (some (.aggregate 0 elems)) mp ∧
        (∃ c, topFrame.locals[arrIdx]? = some ⟨.live (.indirect mp), c⟩) ∧
        topFrame'.locals[arrIdx]? = some ⟨.live (.indirect mp), some arrLay⟩ ∧
        (∀ k, k ≠ arrIdx → topFrame'.locals[k]? = topFrame.locals[k]?) ∧
        topFrame' = { topFrame with locals := topFrame'.locals } ∧
        StateRelLM2_4 body s { m with stack := ⟨#[topFrame']⟩ } ∧
        (SubsliceInBounds count fromIdx toIdx fromEnd →
          evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil body.localDecls =
            .ok (.aggregate 0 ((elems.drop fromIdx).take cnt)) s.frame.locals ∧
          annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) known m =
            .ok ⟨.indirect { mp with
                    ptr := { mp.ptr with
                      offset := Miri.ABI.Size.ofBytes
                        (mp.ptr.offset.bytes + es.bytes * UInt64.ofNat fromIdx) },
                    metadata := .none },
                 { ty := arrLay.ty,
                   layout := { arrLay.layout with
                     fields := .Array es (UInt64.ofNat cnt),
                     size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt) } }⟩
              { m with stack := ⟨#[topFrame']⟩ } ∧
          ∃ (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (baseAddr : UInt64)
            (relOffset : Miri.ABI.Size)
            (localAlloc : Miri.Memory.LocalAllocation AnnealProv
              (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind),
            mp.ptr.provenance = some (.concrete allocId tag) ∧
            (allocId, localAlloc) ∈ m.machine.memory.live.toList ∧
            m.machine.lookupBaseAddr allocId = some baseAddr ∧
            mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes) ∧
            ArraySliceRel elemKind cnt body.layouts ((elems.drop fromIdx).take cnt)
              (Miri.ABI.Size.ofBytes
                (relOffset.bytes + UInt64.ofNat (fromIdx * es.bytes.toNat)))
              localAlloc.allocation) ∧
        (fromEnd = true → count < fromIdx + toIdx → fromIdx + toIdx < 2 ^ 64 →
          evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil body.localDecls =
            .ub ∧
          ∃ msg, annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
            known m = .error (.undefinedBehavior msg) { m with stack := ⟨#[topFrame']⟩ })) := by
  dsimp only
  rcases hstate with
    ⟨tf_s, hframes_s, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have htf_eq : tf_s = topFrame := by
    rw [hframes] at hframes_s
    simpa using hframes_s.symm
  rw [htf_eq] at hretCont hretPlace hframe hdisj
  clear hframes_s htf_eq tf_s
  obtain ⟨slot_arr, mls_arr, _, hlt_arr, hslot_arr, _, hmls_arr_eq, hloc_arr⟩ :=
    hframe.lookup_local hdecl_arr
  let topFrame' :=
    cacheFrameLocalLayout topFrame arrIdx hlt_arr (translateTy arrDecl.ty body.layouts)
  let m' : AnnealStepState := { m with stack := ⟨#[topFrame']⟩ }
  have hcache_arr : ∀ l, (topFrame.locals[arrIdx]'hlt_arr).layout = some l →
      l = translateTy arrDecl.ty body.layouts := by
    rw [hmls_arr_eq]; exact hloc_arr.layout_eq
  have hres_arr : annealResolveAndCacheLocalLayout body.localDecls body.layouts arrIdx known m =
      .ok (topFrame', translateTy arrDecl.ty body.layouts) m' :=
    annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt_arr hdecl_arr hcache_arr
  have hframe' : FrameRelLM2_4 body m.machine s.frame topFrame' :=
    hframe.cache_local_layout hdecl_arr hlt_arr
  have hdisj' : MemoryAllocDisjoint topFrame' := hdisj.cache_layout hlt_arr _
  have hstate' : StateRelLM2_4 body s m' :=
    StateRelLM2_4.mk topFrame' rfl hretCont ⟨retLay, hretPlace⟩ hframe' hcal hstack hbor hprot
      hcaller hdisj'
  have hother' : ∀ k, k ≠ arrIdx → topFrame'.locals[k]? = topFrame.locals[k]? := by
    intro k hk
    unfold topFrame' cacheFrameLocalLayout
    rw [Array.getElem?_set]
    simp [hk.symm]
  have hlt_arr' : arrIdx < topFrame'.locals.size := by
    unfold topFrame' cacheFrameLocalLayout; simp [hlt_arr]
  have hget' : topFrame'.locals[arrIdx]? =
      some { mls_arr with layout := some (translateTy arrDecl.ty body.layouts) } := by
    unfold topFrame' cacheFrameLocalLayout
    rw [Array.getElem?_set, ← hmls_arr_eq]
    simp
  have hval_arr' : (topFrame'.locals[arrIdx]'hlt_arr').value = mls_arr.value := by
    have h := hget'
    rw [Array.getElem?_eq_getElem hlt_arr'] at h
    injection h with h_eq
    rw [h_eq]
  have hnot_empty : m.stack.currentFrame?.isNone = false := by
    rw [stack_currentFrame?_singleton m.stack topFrame hframes]; rfl
  refine ⟨?_, ?_⟩
  · rintro (hdead | ⟨huninit, hcnt⟩)
    · rw [hdead] at hslot_arr; injection hslot_arr with hslot_eq; subst hslot_eq
      have ha_ub : evalOperand s.frame.locals (subsliceReadOperand isMove arrIdx fromIdx toIdx
          fromEnd) .nil s.memory.globals body.layouts .nil body.localDecls = .ub := by
        cases isMove <;> simp [subsliceReadOperand, evalOperand, hdead]
      cases hloc_arr with
      | base _ _ hl =>
        cases hl with
        | dead _ _ =>
          have hgop : topFrame'.getLocalOperand arrIdx = .error (.localExpectedLive arrIdx) := by
            unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
              Miri.Interpreter.LocalState.access
            simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
          refine ⟨ha_ub, m', "read of dead local", ?_⟩
          rw [annealEvalOperandLM2_4_subslice]
          unfold annealEvalSubsliceOperand
          simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, hnot_empty,
            hres_arr, hgop, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
        | immediate _ _ _ _ himm =>
          rcases himm with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
        | indirect _ _ _ _ hnot_dead _ =>
          exact absurd rfl hnot_dead
    · rw [huninit] at hslot_arr; injection hslot_arr with hslot_eq; subst hslot_eq
      have ha_ub : evalOperand s.frame.locals (subsliceReadOperand isMove arrIdx fromIdx toIdx
          fromEnd) .nil s.memory.globals body.layouts .nil body.localDecls = .ub := by
        cases isMove <;> simp [subsliceReadOperand, evalOperand, huninit]
      cases hloc_arr with
      | base _ _ hl =>
        cases hl with
        | immediate _ imm _ _ hval =>
          rcases hval with ⟨_, rfl⟩ | ⟨_, hv, _⟩
          · have hgop : topFrame'.getLocalOperand arrIdx = .ok (.immediate .uninit) := by
              unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
                Miri.Interpreter.LocalState.access
              simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
            refine ⟨ha_ub, m', "projected read of uninitialized local", ?_⟩
            rw [annealEvalOperandLM2_4_subslice]
            unfold annealEvalSubsliceOperand
            simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure,
              EStateM.pure, hnot_empty, hres_arr, hgop, throw, throwThe, MonadExceptOf.throw,
              EStateM.throw]
          · cases hv
        | indirect _ mp _ _ _ hmp =>
          have hgop : topFrame'.getLocalOperand arrIdx = .ok (.indirect mp) := by
            unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
              Miri.Interpreter.LocalState.access
            simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
          have hpos : 0 < count := by
            rcases hcnt with hpos | himm_loc
            · exact hpos
            · exact absurd rfl
                (himm_loc _ (by rw [Array.getElem?_eq_getElem hlt_arr, hmls_arr_eq]) mp)
          have hchk_err := annealCheckIndirectInitialized_uninit_array_ub hwf hnodup hmp hpos
          refine ⟨ha_ub, m', "access to uninitialized indirect place", ?_⟩
          rw [annealEvalOperandLM2_4_subslice]
          unfold annealEvalSubsliceOperand
          simp [m', get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure,
            EStateM.pure, hnot_empty, hres_arr, hgop, hchk_err, throw, throwThe,
            MonadExceptOf.throw, EStateM.throw]
  · intro elems hinit
    rw [hinit] at hslot_arr; injection hslot_arr with hslot_eq; subst hslot_eq
    cases hloc_arr with
    | union _ _ _ _ _ _ _ _ hwt _ _ _ =>
      obtain ⟨n, hn, _⟩ := hwt.fields_union
      rw [hwf.arr_fields] at hn
      cases hn
    | base _ _ hl =>
      obtain ⟨mp, cachedLayout, rfl, _, hmp⟩ := hl.array_init_is_indirect hwf.arr_kind
      have hgop : topFrame'.getLocalOperand arrIdx = .ok (.indirect mp) := by
        unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
          Miri.Interpreter.LocalState.access
        simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
      have hchk_ok : annealCheckIndirectInitialized m.machine mp
          (translateTy arrDecl.ty body.layouts).layout.size = .ok () :=
        annealCheckIndirectInitialized_of_array_memPlaceRel hwf hnodup hmp
      have hsim := evalProjection_subslice_simulation (mach := m.machine) topFrame'
        s.frame.locals hwf hnodup hmp fromIdx toIdx fromEnd
      dsimp only at hsim
      obtain ⟨hin, hoob⟩ := hsim
      refine ⟨mp, topFrame', hmp, ⟨cachedLayout, ?_⟩, hget', hother', rfl, hstate', ?_, ?_⟩
      · rw [Array.getElem?_eq_getElem hlt_arr, hmls_arr_eq]
      · intro hb
        obtain ⟨hr_ok, hpl_ok, hrel⟩ := hin hb
        refine ⟨?_, ?_, hrel⟩
        · cases isMove <;>
            simp [subsliceReadOperand, evalOperand, placeTouchesUnion_subslice_single, hinit, hr_ok]
        · rw [annealEvalOperandLM2_4_subslice]
          unfold annealEvalSubsliceOperand
          simp [m', get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, hnot_empty,
            hres_arr, hgop, hchk_ok, hpl_ok, pure, EStateM.pure]
      · intro he hlt h64
        obtain ⟨hr_ub, msg, hpl_err⟩ := hoob he hlt h64
        refine ⟨?_, msg, ?_⟩
        · cases isMove <;>
            simp [subsliceReadOperand, evalOperand, placeTouchesUnion_subslice_single, hinit, hr_ub]
        · cases hpl : annealProjectList
              (annealSubsliceProjectionCx topFrame' body.layouts m.machine)
              ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩
              [.Subslice fromIdx toIdx fromEnd] with
          | ok _ => simp [hpl, Except.mapError] at hpl_err
          | error pe =>
            simp only [hpl, Except.mapError, Except.error.injEq] at hpl_err
            rw [annealEvalOperandLM2_4_subslice]
            unfold annealEvalSubsliceOperand
            simp [m', get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure,
              EStateM.pure, hnot_empty, hres_arr, hgop, hchk_ok, hpl, hpl_err, throw, throwThe,
              MonadExceptOf.throw, EStateM.throw]

/-! ## 13. Union Cross-Field Type Punning & Sibling Field Writes (`LM-2.4` `D13` Simulation)

With Stage-1 `D13` byte-coherent union projections (`readProjectedValueUnionAware`
and `writeProjectedValueUnionAware`), Anneal and `lean-miri` agree in lockstep on
cross-field union accesses once `_u` holds active field `f`'s (`f < n`) scalar `sc`
(`UnionMemRel`):

1. **Cross-field type-punning read** (`step_union_type_punning_read_simulation`):
   reading a sibling field `_u.j` (`j ≠ f`, `j < n`) of width `w ≤ sc.sizeBytes`
   (whose punned low `w` bytes satisfy scalar validity when `fty` is `bool`/`char`)
   steps both machines in lockstep (`StepRelLM2_4` / `StateRelLM2_4`), decoding
   the low `w` little-endian bytes `sc.bits % scalarModulus w` into `_r`.
2. **Cross-field sibling write** (`step_union_nonzero_field_write_simulation`):
   writing `_u.j = op` (`j < n`, including `j ≠ f`) of width
   `sc.sizeBytes ≤ size(fty) ≤ S` steps both machines in lockstep (`StepRelLM2_4` /
   `StateRelLM2_4`), updating `_u` to `unionSlotFields n j (.scalar sc')` in Anneal
   and overwriting `[0, sc'.sizeBytes)` at offset `0` in `lean-miri` (`UnionMemRel`
   with `IsUnionPrefixMask S sc'.sizeBytes`). -/

/-- Writing any valid scalar prefix `[0, k')` (`k' ≤ S`) on an `S`-byte union
mask with `[0, k)` initialized (`k ≤ S`) succeeds and leaves `[0, max k k')`
initialized (`IsUnionPrefixMask S (max k k')`). -/
theorem IsUnionPrefixMask.setRange_any {S k k' : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hk' : ValidScalarBytes k') (hkS : k ≤ S) (hk'S : k' ≤ S) :
    ∃ M', M.setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes k')) true = .ok M' ∧
      IsUnionPrefixMask S (max k k') M' := by
  by_cases hle : k ≤ k'
  · rw [Nat.max_eq_right hle]
    exact hM.setRange_ge hS hk hk' hle hk'S
  · have hlt : k' < k := by omega
    rw [Nat.max_eq_left (Nat.le_of_lt hlt)]
    refine ⟨M, ?_, hM⟩
    rcases hM with rfl | rfl <;>
      rcases hS with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
      first | omega | with_unfolding_all rfl

/-- **`step_union_type_punning_read_simulation`** (`LM-2.4` `D13`): reading a
sibling field `j ≠ f` (`j < n`) of width `w ≤ sc.sizeBytes` from a union holding
active field `f`'s (`f < n`) value `sc` (`UnionMemRel`) into an immediate scalar
local `_r` (`rDecl.ty = fty`).

Both Anneal (`readProjectedValueUnionAware`) and `lean-miri`
(`Allocation.readScalar` on `[0, w)`) decode the low `w` little-endian bytes
`sc.bits % scalarModulus w` and step in lockstep (`StepRelLM2_4` /
`StateRelLM2_4`; UB in both if `_r` is `.dead`). Together with
`step_union_field_read_simulation`, this covers every scalar union field read
`j < n` of width `w ≤ S` on a `UnionMemRel` union. -/
theorem step_union_type_punning_read_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {r u j : Local} {fty : Ty} {isMove : Bool} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩)
    {rDecl uDecl : LocalDecl}
    (hdecl_r : get? body.localDecls r = some rDecl)
    (hr_ty : rDecl.ty = fty)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hprim : IsPrimScalarTy fty) {w : Nat} (hw : ValidScalarBytes w)
    (hsz : (translateTy fty body.layouts).layout.size = translateSizeBytes w)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n) (hj : j < n)
    {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hr_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame r)
    (hjne : j ≠ f) (hw_le : w ≤ sc.sizeBytes)
    (hbool : fty.kind = .bool → sc.bits % scalarModulus w = 0 ∨ sc.bits % scalarModulus w = 1 :=
      by intro h; nomatch h)
    (hchar : fty.kind = .char → isValidCharCode (sc.bits % scalarModulus w) = true :=
      by intro h; nomatch h)
    (hfl : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size := by exact ⟨_, rfl, rfl⟩) :
    StepRelLM2_4 body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      get? s'.frame.locals r = some (.init (.scalar ⟨sc.bits % scalarModulus w, w⟩))) ∧
    (get? s.frame.locals r ≠ some .dead →
      ∃ (s' : MachineState) (m' : AnnealStepState)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
        (msc_w : Miri.Memory.ScalarInt),
        stepMirFn body s = .step s' ∧
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals r = some (.init (.scalar ⟨sc.bits % scalarModulus w, w⟩)) ∧
        m'.machine = m.machine ∧
        m'.stack.frames = #[tf'] ∧
        ScalarRel ⟨sc.bits % scalarModulus w, w⟩ msc_w ∧
        ∃ c, tf'.locals[r]? = some ⟨.live (.immediate (.scalar (.fromScalarInt msc_w))), c⟩) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot; generalize s.memory = mem; intro hbor hprot
    cases mem; dsimp only at hbor hprot; subst hbor hprot; rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩
      body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
  obtain ⟨c_u, hmls_u⟩ := hu_mls topFrame hframes
  obtain ⟨slot_r0, mls_r0, hlt_af_r, hlt_r0, hslot_r0, _, hmls_r_eq, hloc_r0⟩ :=
    hframe.lookup_local hdecl_r
  have hr_imm0 := hr_imm topFrame hframes
  obtain ⟨_, mls_u0, _, hlt_u0, _, hmls_u0, _, hloc_u0⟩ := hframe.lookup_local hdecl_u
  have hmls_u0' : mls_u0 = ⟨.live (.indirect mp), c_u⟩ := by
    rw [hmls_u] at hmls_u0; exact (Option.some.inj hmls_u0).symm
  have hru : r ≠ u := fun hru => by subst hru; exact hr_imm0 _ hmls_u mp rfl
  let topFrame₀ :=
    cacheFrameLocalLayout topFrame r hlt_r0 (translateTy rDecl.ty body.layouts)
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 r none topFrame.localsIdentity, translateTy rDecl.ty body.layouts⟩
  have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨r, #[]⟩ m =
      .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_r0 hdecl_r
      (by rw [hmls_r_eq]; exact hloc_r0.layout_eq)
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀, cacheFrameLocalLayout]; rw [Array.size_set]; exact hlt_u0
  have hu₀' : topFrame₀.locals[u]? = some ⟨.live (.indirect mp), c_u⟩ := by
    dsimp only [topFrame₀, cacheFrameLocalLayout]
    rw [Array.getElem?_set_ne _ hru]; exact hmls_u
  have hu₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp), c_u⟩ := by
    have h := Array.getElem?_eq_getElem hlt_u₀
    rw [hu₀'] at h; exact (Option.some.inj h).symm
  have hcache_u : ∀ l, (topFrame₀.locals[u]'hlt_u₀).layout = some l →
      l = translateTy uDecl.ty body.layouts := by
    rw [hu₀]; rw [hmls_u0'] at hloc_u0; exact hloc_u0.layout_eq
  obtain ⟨msc0, hmeta, hk_le0, hprim0, himm0⟩ :
      ∃ msc0, mp.metadata = .none ∧ sc.sizeBytes ≤ S ∧ IsPrimScalarTy f0Ty ∧
        ImmediateRel f0Ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc0)) := by
    cases hmem with
    | mk _ _ _ _ msc0 _ _ hm _ _ _ _ _ _ _ _ _ _ _ hkle _ _ hp0 hi0 _ =>
      exact ⟨msc0, hm, hkle, hp0, hi0⟩
  have hop_spec := evalOperand_unionFieldRead_spec (globals := s.memory.globals) (isMove := isMove)
    hdecl_u hprim hw hsz hwt hfields hf hj hprim0 himm0 hk_le0 hfl hu_slot
  have hop_ok := hop_spec.2.1 hjne hw_le hbool hchar
  have hvld : validateLoadedValue body.layouts body.localDecls
      (unionFieldReadOperand isMove u j fty) (.scalar ⟨sc.bits % scalarModulus w, w⟩) = true :=
    validateLoadedValue_unionField_true hdecl_u isMove j fty hbool
  have hrv_ok : evalRvalue s.frame.locals (.use (unionFieldReadOperand isMove u j fty)) s.memory
      body.localDecls body.layouts =
      .ok (.scalar ⟨sc.bits % scalarModulus w, w⟩) s.frame.locals s.memory := by
    unfold evalRvalue; dsimp only
    rw [hbor, hcaller, hop_ok]; dsimp only; rw [hvld]
    cases isMove <;> rfl
  have ha_ok : evalStmt s
      ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩
      body.localDecls body.layouts =
      match get? s.frame.locals r with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? s.frame.locals r (.init (.scalar ⟨sc.bits % scalarModulus w, w⟩)) with
        | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub := by
    unfold evalStmt; dsimp only; rw [hrv_ok]; simp only []
    rw [hprot, hbor]; dsimp only [invalidateConflictingBorrows]; rw [hmem_same]
    cases get? s.frame.locals r with
    | none => rfl
    | some sl =>
      cases sl <;> (try rfl) <;>
        cases set? s.frame.locals r (.init (.scalar ⟨sc.bits % scalarModulus w, w⟩)) <;> rfl
  let topFrame₁ :=
    cacheFrameLocalLayout topFrame₀ u hlt_u₀ (translateTy uDecl.ty body.layouts)
  let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
  have hop : annealEvalOperandLM2_4 body.localDecls body.layouts
      (translateOperand (unionFieldReadOperand isMove u j fty))
      (some (translateTy rDecl.ty body.layouts)) m₀ =
      .ok ⟨.indirect mp, translateTy fty body.layouts⟩ m₁ := by
    have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
    have hfield := annealEvalUnionField_indirect (body := body) (m := m₀) rfl hlt_u₀ hdecl_u
      hcache_u (by rw [hu₀]) hmeta hfields hj hprim
    cases isMove <;>
      simp only [unionFieldReadOperand, translateOperand, translatePlace, List.map,
        translateProjectionElem, List.toArray, annealEvalOperandLM2_4, hunion, ↓reduceIte,
        Bool.false_eq_true] <;>
      exact hfield
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨r, #[]⟩
      (translateRvalue (.use (unionFieldReadOperand isMove u j fty))) = true := by
    have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
    cases isMove <;>
      simp [lm24Assign, lm24Rvalue, lm24Operand, lm24Place, translateRvalue, translateOperand,
        unionFieldReadOperand, translatePlace, hunion]
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩) m =
      Miri.Interpreter.runRvalue
        ((annealReadImmediateLM2_2 ⟨.indirect mp, translateTy fty body.layouts⟩ >>=
          fun imm => annealWriteImmediateLM2_2 imm.imm destPlace)) m₁ := by
    have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
        ⟨r, #[]⟩ true m = .ok destPlace m₀ := hevalPlace_dst
    have hop' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
        (Miri.Interpreter.OperandPath.rvalue "operand")
        (translateOperand (unionFieldReadOperand isMove u j fty))
        (some ((annealRvalueHooksLM2_4 body.localDecls body.layouts).placeLayout destPlace)) m₀ =
        .ok ⟨.indirect mp, translateTy fty body.layouts⟩ m₁ := hop
    have huse : usesMemCopy ⟨.indirect mp, translateTy fty body.layouts⟩ = false := by
      simp [usesMemCopy, hprim.fields_primitive]
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace']
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop']
    simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2, huse, Bool.false_eq_true, ↓reduceIte]
  have hS := hwt.size_valid
  have hS16 : S ≤ 16 := by rcases hS with h | h | h | h | h <;> omega
  obtain ⟨msc_w, hrel_w, hread_imm⟩ : ∃ msc_w : Miri.Memory.ScalarInt,
      ScalarRel ⟨sc.bits % scalarModulus w, w⟩ msc_w ∧
      annealReadImmediateLM2_2 ⟨.indirect mp, translateTy fty body.layouts⟩ m₁ =
        .ok ⟨.scalar (.fromScalarInt msc_w), translateTy fty body.layouts⟩ m₁ := by
    cases hmem with
    | mk allocId tag baseAddr localAlloc msc hprov _ _ hlive hbase hptr _ hsize hlen _ _ _ _ _
        hk_le hmask hrel _ _ hraw =>
      have hfind := array_find?_of_nodup_fst hnodup hlive
      have hrel_off : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = Miri.ABI.Size.ZERO := by
        have hb : mp.ptr.offset.bytes = baseAddr := by rw [hptr]; rfl
        rw [hb, UInt64.sub_self]; rfl
      have hfields_f := hprim.fields_primitive (layouts := body.layouts)
      have hsz0_f := hprim.size_beq_zero (layouts := body.layouts)
      obtain ⟨s_repr, hrepr_f⟩ := hprim.backendRepr_scalar (layouts := body.layouts)
      have hinit := hmask.init hS hrel.validBytes hw hk_le hw_le
      obtain ⟨msc_w, hrel_w, hread_sc⟩ :=
        union_readScalar_prefix_le hw hlen hsize hS16 hw_le hk_le hinit hraw
      refine ⟨msc_w, hrel_w, ?_⟩
      unfold annealReadImmediateLM2_2 annealReadIndirectImmediate
      dsimp only
      rw [hprov, hfields_f, hsz0_f, hrepr_f, hsz]
      simp only [Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get,
        bind, EStateM.bind, Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind,
        hrel_off, hread_sc, pure, EStateM.pure, m₁]
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc_w)) destPlace) m₁ := by
    rw [hm_eval]
    apply runRvalue_eq_of_eq
    exact EStateM.bind_eq_ok hread_imm
  have hframe₁ : FrameRelLM2_4 body m.machine s.frame topFrame₁ :=
    (hframe.cache_local_layout hdecl_r hlt_r0).cache_local_layout hdecl_u hlt_u₀
  have hdisj₁ : MemoryAllocDisjoint topFrame₁ :=
    (hdisj.cache_layout hlt_r0 _).cache_layout hlt_u₀ _
  have hr_imm₁ : IsImmediateFrameLocal topFrame₁ r :=
    (hr_imm0.cache_layout hlt_r0 _).cache_layout hlt_u₀ _
  have hretCont₁ : topFrame₁.returnContinuation = .stop false := hretCont
  have hretPlace₁ : ∃ retLay, topFrame₁.returnPlace =
      .frameLocal 0 0 none retLay topFrame₁.localsIdentity := ⟨retLay, hretPlace⟩
  have himm_r : ImmediateRel rDecl.ty body.layouts (.scalar ⟨sc.bits % scalarModulus w, w⟩)
      (.scalar (.fromScalarInt msc_w)) := by
    rw [hr_ty]
    refine .scalar _ _ hrel_w hsz (fun hk => ?_) (fun hk => ?_)
    · have hw1 : w = 1 := translateSizeBytes_inj hw (Or.inl rfl)
        (by rw [← hsz]; simp [translateTy, hk]; rfl)
      exact ⟨hw1, hbool hk⟩
    · have hw4 : w = 4 := translateSizeBytes_inj hw (Or.inr (Or.inr (Or.inl rfl)))
        (by rw [← hsz]; simp [translateTy, hk]; rfl)
      exact ⟨hw4, hchar hk⟩
  have hext := write_after_rvalue_simulation_LM2_4
    (annealStepHooksLM2_4 body.localDecls body.layouts)
    hretCont₁ hretPlace₁ hcal hstack hbor hprot hcaller hframes hframe.body_eq
    hframe.location_eq hbb hstmt hframe₁ hdisj₁ hdecl_r hr_imm₁ himm_r ha_ok hm_write
  have hpost_r : ∀ s', stepMirFn body s = .step s' →
      get? s'.frame.locals r = some (.init (.scalar ⟨sc.bits % scalarModulus w, w⟩)) := by
    intro s' hs'
    rw [hstep_a, ha_ok, hslot_r0] at hs'
    split at hs'
    · exact absurd hs' MirStepNode_fail_ne_step
    · rw [set?_eq_some_set hlt_af_r] at hs'
      have hs'' := MirStepNode_step_inj hs'
      subst hs''
      simp [advanceStmt, get?_eq_getElem?, hlt_af_r]
    · exact absurd hs' MirStepNode_fail_ne_step
  refine ⟨by rw [hstep_a]; exact hext.1, hpost_r, fun hr_live => ?_⟩
  have hs_step : ∃ s', stepMirFn body s = .step s' := by
    rw [hstep_a, ha_ok]
    cases hsr : slot_r0 with
    | dead => rw [hsr] at hslot_r0; exact absurd hslot_r0 hr_live
    | uninit => rw [hsr] at hslot_r0; rw [hslot_r0, set?_eq_some_set hlt_af_r]; exact ⟨_, rfl⟩
    | init v => rw [hsr] at hslot_r0; rw [hslot_r0, set?_eq_some_set hlt_af_r]; exact ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ := hs_step
  obtain ⟨slot_r, mls_r1, _, hlt_r1, hslot_r1, hmls_r1, hmls_r1_eq, hloc_r1⟩ :=
    hframe₁.lookup_local hdecl_r
  have hget_r1 := frame_getLocal_of_getElem? topFrame₁ r mls_r1 hmls_r1
  have himm_r1 := hr_imm₁ mls_r1 hmls_r1
  rcases mls_r1 with ⟨vr, cr⟩
  cases vr with
  | dead =>
    cases hloc_r1 with
    | base _ _ hl =>
      cases hl with
      | dead _ _ => exact absurd hslot_r1 hr_live
  | live opr =>
    cases opr with
    | indirect mpr => exact False.elim (himm_r1 mpr rfl)
    | immediate _ =>
      let topFrame₂ :=
        { topFrame₁ with
          locals := topFrame₁.locals.set r
            { topFrame₁.locals[r]'hlt_r1 with
              value := .live (.immediate (.scalar (.fromScalarInt msc_w))) } hlt_r1 }
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_4 body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩) m =
          ({ m with stack := ⟨#[topFrame₂]⟩ }, .ok ()) := by
        rw [hm_write]
        unfold Miri.Interpreter.runRvalue
        rw [annealWriteImmediateLM2_2_live (m := m₁) (topFrame := topFrame₁) rfl hlt_r1 hget_r1]
      have hloc₂ : topFrame₂.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
        hframe₁.location_eq
      have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
        hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ok rfl hloc₂
      have hrel_step := hext.1
      rw [← hstep_a, hs', hstep_m] at hrel_step
      cases hrel_step with
      | step _ _ hst' =>
        refine ⟨s', _,
          { topFrame₂ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ },
          msc_w, hs', hstep_m, hst', hpost_r s' hs', rfl, rfl, hrel_w,
          ⟨(topFrame₁.locals[r]'hlt_r1).layout, ?_⟩⟩
        dsimp only [topFrame₂]
        rw [Array.getElem?_set_self]

/-- **`step_union_nonzero_field_write_simulation`** (`LM-2.4` `D13`): the
projected write `_u.j = op` (`j < n`, including sibling writes `j ≠ f`) into a
scalar field `fty` of width `sc.sizeBytes ≤ size(fty) ≤ S` on a union that
already holds active field `f`'s (`f < n`) value `sc` (`UnionMemRel`).

Both Anneal (`writeProjectedForLocal` / `writeProjectedValueUnionAware`) and
`lean-miri` (`annealEvalUnionFieldPlace` + `annealWriteImmediateLM2_2`) step in
lockstep (`StepRelLM2_4` / `StateRelLM2_4`): UB in both if `op` reads a
dead/uninitialized local, and otherwise `_u` becomes
`unionSlotFields n j (.scalar sc')` backed by `UnionMemRel` for `(fty, sc')`
(`IsUnionPrefixMask S sc'.sizeBytes`) with `0` fresh allocations. -/
theorem step_union_nonzero_field_write_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {u j : Local} {fty : Ty} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩)
    {uDecl : LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n) (hj : j < n)
    {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c', topFrame.locals[u]? = some ⟨.live (.indirect mp), c'⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hprim : IsPrimScalarTy fty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op fty)
    (hk_ge_ty : sc.sizeBytes ≤ (translateTy fty body.layouts).layout.size.bytes.toNat)
    (hfty_le : (translateTy fty body.layouts).layout.size.bytes.toNat ≤ S)
    (hfl0 : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size := by exact ⟨_, rfl, rfl⟩)
    (hfl' : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) j = some fl ∧
      fl.layout.size = (translateTy fty body.layouts).layout.size := by exact ⟨_, rfl, rfl⟩) :
    StepRelLM2_4 body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      ∃ (sc' : MirAst.ScalarInt) (m' : AnnealStepState)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
          .ok (.scalar sc') s.frame.locals ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals u = some (.init (.aggregate 0 (unionSlotFields n j (.scalar sc')))) ∧
        (∀ k, k ≠ u → get? s'.frame.locals k = get? s.frame.locals k) ∧
        m'.stack.frames = #[tf'] ∧
        (∃ c', tf'.locals[u]? = some ⟨.live (.indirect mp), c'⟩) ∧
        UnionMemRel m'.machine uDecl.ty body.layouts S fty sc' mp ∧
        LiveAllocsNodup m'.machine ∧
        (∀ tf, m.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) ∧
        s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
        StepPreservesHighWater m 0 (m', .ok true)) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have hop_tf := hop topFrame hframes
  have hop_ld := hop_tf.evalOperand_localDecls_eq s.frame.locals s.memory.globals
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot; generalize s.memory = mem; intro hbor hprot
    cases mem; dsimp only at hbor hprot; subst hbor hprot; rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩ body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
  obtain ⟨c_u, hmls_u⟩ := hu_mls topFrame hframes
  obtain ⟨_, mls_u, hlt_af_u, hlt_u, _, hmls_u', hmls_u_eq, hloc_u⟩ := hframe.lookup_local hdecl_u
  rw [hmls_u] at hmls_u'; injection hmls_u' with hmls_u'; subst hmls_u'
  have hcache_u := hloc_u.layout_eq
  obtain ⟨msc0, hmeta, hk_le0, hprim0, himm0⟩ :
      ∃ msc0, mp.metadata = .none ∧ sc.sizeBytes ≤ S ∧ IsPrimScalarTy f0Ty ∧
        ImmediateRel f0Ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc0)) := by
    cases hmem with
    | mk _ _ _ _ msc0 _ _ hm _ _ _ _ _ _ _ _ _ _ _ hkle _ _ hp0 hi0 _ =>
      exact ⟨msc0, hm, hkle, hp0, hi0⟩
  have hS := hwt.size_valid
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame u hlt_u layU
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  have hplace : annealEvalUnionFieldPlace body.localDecls body.layouts u j (encodeTyId fty) m =
      .ok ⟨.memory mp, translateTy fty body.layouts⟩ m₀ :=
    annealEvalUnionFieldPlace_indirect hframes hlt_u hdecl_u (by rw [hmls_u_eq]; exact hcache_u)
      (by rw [hmls_u_eq]) hmeta hfields hj hprim
  have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
  have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
      ⟨u, #[.Field j (encodeTyId fty)]⟩ true m =
      .ok ⟨.memory mp, translateTy fty body.layouts⟩ m₀ := by
    show annealEvalPlaceLM2_4 body.localDecls body.layouts ⟨u, #[.Field j (encodeTyId fty)]⟩ m = _
    simp only [annealEvalPlaceLM2_4, hunion, ↓reduceIte]
    exact hplace
  have hframe₀ : FrameRelLM2_4 body m.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_u hlt_u
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ := hdisj.cache_layout hlt_u _
  have hop₀ : WellTypedScalarOperand body topFrame₀ op fty := hop_tf.cache_layout hlt_u layU
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨u, #[.Field j (encodeTyId fty)]⟩
      (translateRvalue (.use op)) = true := by
    simp [lm24Assign, lm24Place, hunion]
  have hm_pre : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
          (some (translateTy fty body.layouts)) >>= fun o =>
          (annealRvalueHooksLM2_4 body.localDecls body.layouts).copyOp () o
            ⟨.memory mp, translateTy fty body.layouts⟩) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateProjectionElem]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace']
    dsimp only [translateRvalue]
    rfl
  have hlm_eq : ∀ st, annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
      (some (translateTy fty body.layouts)) st =
      annealEvalOperand body.localDecls body.layouts (translateOperand op)
        (some (translateTy fty body.layouts)) st := fun st => by
    rw [annealEvalOperandLM2_4_scalar hop₀]
  have hcopy_imm : ∀ (imm : Miri.Interpreter.Immediate AnnealProv)
      (lay : Miri.Interpreter.LocalLayout) (st : AnnealStepState),
      (annealRvalueHooksLM2_4 body.localDecls body.layouts).copyOp () ⟨.immediate imm, lay⟩
          ⟨.memory mp, translateTy fty body.layouts⟩ st =
        (annealReadImmediateLM2_2 ⟨.immediate imm, lay⟩ >>= fun i =>
          annealWriteImmediateLM2_2 i.imm ⟨.memory mp, translateTy fty body.layouts⟩) st := by
    intro imm lay st; rfl
  rcases evalScalarOperand_LM2_4 hframe₀ hprim hop₀ s.memory.globals
      (some (translateTy fty body.layouts)) with
    ⟨ha_ub, ⟨m_err, msg, hm_err⟩ | ⟨lay, st', hm_uninit⟩⟩ |
    ⟨sc', msc', tf₁, ha_ok, hm_ok, hframe₁, hdisj₁, hmono₁, htf₁, hind₁, hrel', himm'⟩
  · have ha : evalStmt s ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue; dsimp only; rw [hbor, hcaller, hop_ld, ha_ub]
    have hm_err' : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        (some (translateTy fty body.layouts)) m₀ = .error (.undefinedBehavior msg) m_err := by
      rw [hlm_eq]; exact hm_err
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩) m =
        (m_err, .error (.undefinedBehavior msg)) := by
      rw [hm_pre]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hm_err']
    rw [hstep_a, ha, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_stmt]
    exact ⟨.ub _ _, fun _ h => absurd h MirStepNode_fail_ne_step⟩
  · have ha : evalStmt s ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue; dsimp only; rw [hbor, hcaller, hop_ld, ha_ub]
    have hm_uninit' : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        (some (translateTy fty body.layouts)) m₀ = .ok ⟨.immediate .uninit, lay⟩ st' := by
      rw [hlm_eq]; exact hm_uninit
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩) m =
        (st', .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_pre]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hm_uninit', hcopy_imm]; rfl
    rw [hstep_a, ha, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_stmt]
    exact ⟨.ub _ _, fun _ h => absurd h MirStepNode_fail_ne_step⟩
  · cases himm' with
    | scalar _ _ hrel'_sc hsz' hbool' hchar' =>
    have himm' : ImmediateRel fty body.layouts (.scalar sc') (.scalar (.fromScalarInt msc')) :=
      .scalar sc' msc' hrel'_sc hsz' hbool' hchar'
    have hk'_toNat : (translateTy fty body.layouts).layout.size.bytes.toNat = sc'.sizeBytes := by
      rw [hsz']; exact translateSizeBytes_toNat_of_valid hrel'.validBytes
    have hk_ge : sc.sizeBytes ≤ sc'.sizeBytes := by rw [← hk'_toNat]; exact hk_ge_ty
    have hk'_le : sc'.sizeBytes ≤ S := by rw [← hk'_toNat]; exact hfty_le
    obtain ⟨allocIdx, allocId, kind, A', la₀, hprov_a, hlive₀, hw, hmem', hnodup', hother⟩ :=
      annealWriteImmediate_unionInplace_ge (tf := tf₁) (destLay := translateTy fty body.layouts)
        hnodup hmem hS hprim hrel' hk_ge hk'_le himm'
    let mach₃ := inplaceMachine m.machine allocIdx allocId kind A'
    have hm_ok' : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        (some (translateTy fty body.layouts)) m₀ =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc')), translateTy fty body.layouts⟩
          { stack := ⟨#[tf₁]⟩, machine := m.machine } := by
      rw [hlm_eq]; exact hm_ok
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩) m =
        ({ stack := ⟨#[tf₁]⟩, machine := mach₃ }, .ok ()) := by
      rw [hm_pre]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hm_ok', hcopy_imm]
      simp only [bind, EStateM.bind, annealReadImmediateLM2_2, pure, EStateM.pure]
      rw [hw]
    have htf₁_loc : tf₁.location = topFrame.location := by rw [htf₁]; rfl
    have htf₁_body : tf₁.body = topFrame.body := by rw [htf₁]; rfl
    have htf₁_rc : tf₁.returnContinuation = topFrame.returnContinuation := by rw [htf₁]; rfl
    have htf₁_rp : tf₁.returnPlace = topFrame.returnPlace := by rw [htf₁]; rfl
    have htf₁_id : tf₁.localsIdentity = topFrame.localsIdentity := by rw [htf₁]; rfl
    have hloc₁ : tf₁.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
      rw [htf₁_loc]; exact hframe.location_eq
    have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
      hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl hloc₁
    have hvld := (WellTypedLM2_1ScalarOperand.ofScalar hop_tf).validateLoadedValue_true hbool'
    have hrv : evalRvalue s.frame.locals (.use op) s.memory body.localDecls body.layouts =
        .ok (.scalar sc') s.frame.locals s.memory := by
      unfold evalRvalue; dsimp only; rw [hbor, hcaller, hop_ld, ha_ok]; dsimp only; rw [hvld]
      simp only []
    have hwp := writeProjectedForLocal_union_field_ge (locals := s.frame.locals) hdecl_u hwt
      hfields hf hj hprim0 himm0 hfl0 hprim himm' hk_ge hk'_le hfl'
    let locals₂ := s.frame.locals.set u (.init (.aggregate 0 (unionSlotFields n j (.scalar sc'))))
    have ha_ok' : evalStmt s ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.step (advanceStmt s locals₂ s.memory) := by
      unfold evalStmt; dsimp only; rw [hrv]; simp only []
      rw [hu_slot]; dsimp only
      rw [hwp]; dsimp only
      rw [set?_eq_some_set hlt_af_u, hprot, hbor]
      dsimp only [invalidateConflictingBorrowsAtProj]
      rw [hmem_same]
    have hu₀ : topFrame₀.locals[u]? = some ⟨.live (.indirect mp), some layU⟩ := by
      dsimp only [topFrame₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set_self]; simp [hmls_u_eq]
    have hu₁ : tf₁.locals[u]? = some ⟨.live (.indirect mp), some layU⟩ := by
      rw [hind₁ u mp (some layU) hu₀, hu₀]
    have hdisj₁' := hdisj₁ hdisj₀
    let tf_fin := { tf₁ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
    let m' : AnnealStepState := { stack := ⟨#[tf_fin]⟩, machine := mach₃ }
    have hframe_fin : FrameRelLM2_4 body mach₃ (advanceStmt s locals₂ s.memory).frame tf_fin :=
      { body_eq := by show tf₁.body = _; rw [htf₁_body]; exact hframe.body_eq
        location_eq := rfl
        af_locals_len := by
          show (s.frame.locals.set u _).length = _; rw [List.length_set]; exact hframe.af_locals_len
        mf_locals_size := hframe₁.mf_locals_size
        locals_rel := by
          intro i decl slot mls hdecl hslot hmls
          have hslot' : get? locals₂ i = some slot := hslot
          have hmls' : tf₁.locals[i]? = some mls := hmls
          rw [get?_eq_getElem?, List.getElem?_set] at hslot'
          by_cases hiu : u = i
          · subst hiu
            simp only [↓reduceIte, hlt_af_u, Option.some.injEq] at hslot'
            subst hslot'
            rw [hu₁] at hmls'; injection hmls' with hmls'; subst hmls'
            rw [hdecl_u] at hdecl; cases hdecl
            exact .union S n j fty sc' mp _ (fun l hl => (Option.some.inj hl).symm) hwt hfields
              hj hmem'
          · simp only [hiu, ↓reduceIte] at hslot'
            have hloc := hframe₁.locals_rel i decl slot mls hdecl hslot' hmls'
            refine hloc.of_entry ?_
            intro mp_i c_i hmi a la hpa hla
            subst hmi
            have hne_a : a ≠ allocId := by
              intro hae; subst hae
              have := hdisj₁' u i mp mp_i (some layU) c_i hiu hu₁ hmls'
              rw [hprov_a, hpa] at this; exact this rfl
            exact ⟨hother a la hne_a hla, rfl⟩ }
    have hstate' : StateRelLM2_4 body (advanceStmt s locals₂ s.memory) m' :=
      StateRelLM2_4.mk tf_fin rfl (by show tf₁.returnContinuation = _; rw [htf₁_rc]; exact hretCont)
        ⟨retLay, by show tf₁.returnPlace = .frameLocal 0 0 none retLay tf₁.localsIdentity
                    rw [htf₁_rp, htf₁_id]; exact hretPlace⟩
        hframe_fin hcal hstack hbor hprot hcaller hdisj₁'
    rw [hstep_a, ha_ok', hstep_m]
    refine ⟨.step _ _ hstate', fun s'' hs'' => ?_⟩
    have hs''' := MirStepNode_step_inj hs''
    subst hs'''
    refine ⟨sc', m', tf_fin, rfl, ha_ok, hstate', ?_, ?_, rfl, ⟨some layU, hu₁⟩, hmem', hnodup',
      ?_, rfl, rfl, ?_⟩
    · simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_u]
    · intro k hk
      simp [advanceStmt, locals₂, get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hk)]
    · intro tf htf k himm_k
      rw [hframes] at htf
      have htf' : topFrame = tf := by simpa using htf
      subst htf'
      exact hmono₁ k (himm_k.cache_layout hlt_u layU)
    · intro _ hw0 _
      obtain ⟨hw', hnext⟩ := MemoryHighWater.inplaceMachine (kind := kind) (alloc := A')
        (allocIdx := allocIdx) hw0 hlive₀
      exact ⟨hw', by rw [hnext]; omega⟩

/-- Spliced little-endian scalar obtained by overwriting the low `sc'.sizeBytes`
bytes of `sc_old` with `sc'` while retaining `sc_old`'s high bytes
`[sc'.sizeBytes, sc_old.sizeBytes)`. -/
def unionSpliceLowScalar (sc_old sc' : MirAst.ScalarInt) : MirAst.ScalarInt :=
  { bits := sc'.bits + (sc_old.bits / scalarModulus sc'.sizeBytes) * scalarModulus sc'.sizeBytes
    sizeBytes := sc_old.sizeBytes }

private theorem unionSpliceLowScalar_canonical {sc_old sc' : MirAst.ScalarInt}
    (hle : sc'.sizeBytes ≤ sc_old.sizeBytes)
    (hcan' : sc'.bits < scalarModulus sc'.sizeBytes)
    (hcan_old : sc_old.bits < scalarModulus sc_old.sizeBytes) :
    (unionSpliceLowScalar sc_old sc').bits < scalarModulus sc_old.sizeBytes := by
  dsimp only [unionSpliceLowScalar]
  rw [scalarModulus_eq_two_pow] at hcan' hcan_old
  rw [scalarModulus_eq_two_pow, scalarModulus_eq_two_pow]
  have hpow : 2 ^ (8 * sc_old.sizeBytes) =
      2 ^ (8 * (sc_old.sizeBytes - sc'.sizeBytes)) * 2 ^ (8 * sc'.sizeBytes) := by
    rw [← Nat.pow_add]
    congr 1; omega
  have hdiv_lt : sc_old.bits / 2 ^ (8 * sc'.sizeBytes) <
      2 ^ (8 * (sc_old.sizeBytes - sc'.sizeBytes)) := by
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm, ← hpow]
    exact hcan_old
  have hdiv_le :
      (sc_old.bits / 2 ^ (8 * sc'.sizeBytes) + 1) * 2 ^ (8 * sc'.sizeBytes) ≤
        2 ^ (8 * sc_old.sizeBytes) := by
    rw [hpow]
    exact Nat.mul_le_mul_right _ hdiv_lt
  have hadd :
      sc'.bits + (sc_old.bits / 2 ^ (8 * sc'.sizeBytes)) * 2 ^ (8 * sc'.sizeBytes) <
        (sc_old.bits / 2 ^ (8 * sc'.sizeBytes) + 1) * 2 ^ (8 * sc'.sizeBytes) := by
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm _ (2 ^ (8 * sc'.sizeBytes))]
    exact Nat.add_lt_add_right hcan' _
  exact Nat.lt_of_lt_of_le hadd hdiv_le

private theorem allocLeBytes_unionSpliceLowScalar
    {E : Type} {A A' : Miri.Memory.Allocation AnnealProv E} {S : Nat}
    {sc_old sc' : MirAst.ScalarInt}
    (hlen_old : A.len = S) (hlen' : A'.len = S)
    (_hk_lt : sc'.sizeBytes < sc_old.sizeBytes) (hk_old : sc_old.sizeBytes ≤ S)
    (hcan' : sc'.bits < scalarModulus sc'.sizeBytes)
    (hlow : (unionAllocRaw A').extract 0 sc'.sizeBytes = allocLeBytes sc'.bits sc'.sizeBytes)
    (hhigh : (unionAllocRaw A').extract sc'.sizeBytes S =
      (unionAllocRaw A).extract sc'.sizeBytes S)
    (hold : (unionAllocRaw A).extract 0 sc_old.sizeBytes = allocLeBytes sc_old.bits sc_old.sizeBytes) :
    (unionAllocRaw A').extract 0 sc_old.sizeBytes =
      allocLeBytes (unionSpliceLowScalar sc_old sc').bits sc_old.sizeBytes := by
  have hraw'_sz : (unionAllocRaw A').size = S := hlen'
  have hraw_sz : (unionAllocRaw A).size = S := hlen_old
  apply Array.ext
  · simp [hraw'_sz, allocLeBytes_size, Nat.min_eq_left hk_old]
  · intro i hi₁ hi₂
    simp only [Array.size_extract, hraw'_sz, Nat.sub_zero, Nat.min_eq_left hk_old] at hi₁
    rw [Array.getElem_extract]
    simp only [Nat.zero_add, allocLeBytes, List.getElem_toArray, List.getElem_map,
      List.getElem_range', Nat.one_mul, unionSpliceLowScalar, scalarModulus_eq_two_pow]
    by_cases hiw : i < sc'.sizeBytes
    · have hex_low := congrArg (fun a => a[i]?) hlow
      have hi_ext' : i < ((unionAllocRaw A').extract 0 sc'.sizeBytes).size := by
        simp [hraw'_sz]; omega
      have hi_le' : i < (allocLeBytes sc'.bits sc'.sizeBytes).size := by
        simp [allocLeBytes_size]; exact hiw
      rw [Array.getElem?_eq_getElem hi_ext', Array.getElem?_eq_getElem hi_le',
        Array.getElem_extract] at hex_low
      simp only [Option.some.injEq, Nat.zero_add, allocLeBytes, List.getElem_toArray,
        List.getElem_map, List.getElem_range', Nat.one_mul] at hex_low
      rw [hex_low]
      have hsplit : 8 * sc'.sizeBytes = 8 * i + (8 * (sc'.sizeBytes - 1 - i) + 8) := by omega
      have hpow_w : 2 ^ (8 * sc'.sizeBytes) =
          (2 ^ (8 * (sc'.sizeBytes - 1 - i)) * 256) * 2 ^ (8 * i) := by
        rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.mul_comm (2 ^ (8 * i))]
      have hmul_assoc :
          (sc_old.bits / 2 ^ (8 * sc'.sizeBytes)) * 2 ^ (8 * sc'.sizeBytes) =
            ((sc_old.bits / 2 ^ (8 * sc'.sizeBytes)) *
              (2 ^ (8 * (sc'.sizeBytes - 1 - i)) * 256)) * 2 ^ (8 * i) :=
        calc
          (sc_old.bits / 2 ^ (8 * sc'.sizeBytes)) * 2 ^ (8 * sc'.sizeBytes) =
              (sc_old.bits / 2 ^ (8 * sc'.sizeBytes)) *
                ((2 ^ (8 * (sc'.sizeBytes - 1 - i)) * 256) * 2 ^ (8 * i)) :=
            congrArg _ hpow_w
          _ = ((sc_old.bits / 2 ^ (8 * sc'.sizeBytes)) *
                (2 ^ (8 * (sc'.sizeBytes - 1 - i)) * 256)) * 2 ^ (8 * i) :=
            (Nat.mul_assoc _ _ _).symm
      rw [hmul_assoc,
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos (8 * i)),
        ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
    · have hw_le_i : sc'.sizeBytes ≤ i := by omega
      have hex_hi := congrArg (fun a => a[i - sc'.sizeBytes]?) hhigh
      have hi_hi' : i - sc'.sizeBytes < ((unionAllocRaw A').extract sc'.sizeBytes S).size := by
        simp [hraw'_sz]; omega
      have hi_hi : i - sc'.sizeBytes < ((unionAllocRaw A).extract sc'.sizeBytes S).size := by
        simp [hraw_sz]; omega
      rw [Array.getElem?_eq_getElem hi_hi', Array.getElem?_eq_getElem hi_hi,
        Array.getElem_extract, Array.getElem_extract] at hex_hi
      simp only [Option.some.injEq, Nat.add_sub_cancel' hw_le_i] at hex_hi
      have hex_old := congrArg (fun a => a[i]?) hold
      have hi_old : i < ((unionAllocRaw A).extract 0 sc_old.sizeBytes).size := by
        simp [hraw_sz, Nat.min_eq_left hk_old]; exact hi₁
      have hi_le_old : i < (allocLeBytes sc_old.bits sc_old.sizeBytes).size := by
        simp [allocLeBytes_size]; exact hi₁
      rw [Array.getElem?_eq_getElem hi_old, Array.getElem?_eq_getElem hi_le_old,
        Array.getElem_extract] at hex_old
      simp only [Option.some.injEq, Nat.zero_add, allocLeBytes, List.getElem_toArray,
        List.getElem_map, List.getElem_range', Nat.one_mul] at hex_old
      rw [hex_hi, hex_old]
      have hcan'_pow : sc'.bits < 2 ^ (8 * sc'.sizeBytes) := by
        rwa [scalarModulus_eq_two_pow] at hcan'
      have hpow_i : 2 ^ (8 * i) = 2 ^ (8 * sc'.sizeBytes) * 2 ^ (8 * (i - sc'.sizeBytes)) := by
        rw [← Nat.pow_add]; congr 1; omega
      have hrhs :
          (sc'.bits + sc_old.bits / 2 ^ (8 * sc'.sizeBytes) * 2 ^ (8 * sc'.sizeBytes)) /
            2 ^ (8 * i) = sc_old.bits / 2 ^ (8 * i) :=
        calc
          (sc'.bits + sc_old.bits / 2 ^ (8 * sc'.sizeBytes) * 2 ^ (8 * sc'.sizeBytes)) /
              2 ^ (8 * i) =
              (sc'.bits + sc_old.bits / 2 ^ (8 * sc'.sizeBytes) * 2 ^ (8 * sc'.sizeBytes)) /
                (2 ^ (8 * sc'.sizeBytes) * 2 ^ (8 * (i - sc'.sizeBytes))) := by
            rw [hpow_i]
          _ = ((sc'.bits + sc_old.bits / 2 ^ (8 * sc'.sizeBytes) * 2 ^ (8 * sc'.sizeBytes)) /
                2 ^ (8 * sc'.sizeBytes)) / 2 ^ (8 * (i - sc'.sizeBytes)) := by
            rw [← Nat.div_div_eq_div_mul]
          _ = (sc_old.bits / 2 ^ (8 * sc'.sizeBytes)) / 2 ^ (8 * (i - sc'.sizeBytes)) := by
            rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos (8 * sc'.sizeBytes)),
              Nat.div_eq_of_lt hcan'_pow, Nat.zero_add]
          _ = sc_old.bits / 2 ^ (8 * i) := by
            rw [Nat.div_div_eq_div_mul, ← hpow_i]
      rw [hrhs]

/-- **`step_union_narrower_field_write_correspondence`** (`D13a` raw-byte retention
across narrower projected union field writes): unlike unprojected aggregate
overwrite `_u = U { field_f: op }` (`step_union_aggregate_smaller_overwrite_divergence`),
a **projected** narrower scalar field write `_u.j = op` (`w_j < sc_old.sizeBytes ≤ S`)
on an initialized `n`-field union `_u` holding `sc_old` (`UnionMemRel`) preserves
the trailing high bytes `[w_j, sc_old.sizeBytes)` in **both** machines:
1. If `op` faults with `.ub` (dead or uninitialized operand), both `stepMirFn`
   and `Miri.Interpreter.Step.step` fault with `.ub` (`StepRelLM2_4`).
2. When `op` evaluates to `.scalar sc'` (`sc'.sizeBytes < sc_old.sizeBytes`):
   - Anneal (`writeProjectedForLocal_union_field_lt`) updates `_u` to
     `unionSlotFields n j (.scalar sc') ++ [.aggregate 0 (encodeRawAbstractByteVals mergedBytes)]`,
     attaching the `D13a` raw-byte overlay that retains `sc_old`'s high bytes
     `[sc'.sizeBytes, sc_old.sizeBytes)`;
   - `lean-miri` rewrites `[0, sc'.sizeBytes)` in place (`0` fresh allocations),
     preserves `IsUnionPrefixMask S sc_old.sizeBytes`, preserves all trailing
     bytes `(unionAllocRaw A').extract sc'.sizeBytes S = (unionAllocRaw A).extract sc'.sizeBytes S`,
     and — for any integer/unsigned wide field `f0Ty` (`f0Ty.kind ≠ .bool`,
     `f0Ty.kind ≠ .char`) — establishes `UnionMemRel` for the spliced scalar
     `unionSpliceLowScalar sc_old sc'`.

This is a correspondence, not a `StateRelLM2_4` simulation: `UnionLocalRel.union`
relates only plain union values `.aggregate 0 (unionSlotFields n f (.scalar sc))`,
so the overlay-carrying post-state of `_u` is related to `lean-miri` memory only
through `UnionMemRel` for `unionSpliceLowScalar sc_old sc'` and the explicit
per-local facts above, not through `StateRelLM2_4 body s' m'`. Further union steps
from that state (for example a second narrower write, which needs a plain
`hu_slot`) are not covered until `UnionLocalRel` gains an overlay case. -/
theorem step_union_narrower_field_write_correspondence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {u j : Local} {fty : Ty} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩)
    {uDecl : LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n) (hj : j < n)
    {f0Ty : Ty} {sc_old : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc_old)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c', topFrame.locals[u]? = some ⟨.live (.indirect mp), c'⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc_old mp)
    (hprim : IsPrimScalarTy fty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op fty)
    (hlt_width : (translateTy fty body.layouts).layout.size.bytes.toNat < sc_old.sizeBytes)
    (hfl0 : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size := by exact ⟨_, rfl, rfl⟩)
    (hfl' : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) j = some fl ∧
      fl.layout.size = (translateTy fty body.layouts).layout.size := by exact ⟨_, rfl, rfl⟩) :
    (evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = .ub →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ sc', evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
        .ok (.scalar sc') s.frame.locals →
      let mergedBytes :=
        encodeLittleEndianBytes sc'.bits sc'.sizeBytes none ++
          ((encodeLittleEndianBytes sc_old.bits sc_old.sizeBytes none).drop sc'.sizeBytes ++
            replicateUninitBytes (S - sc_old.sizeBytes))
      let s' := advanceStmt s
        (s.frame.locals.set u (.init (.aggregate 0
          (unionSlotFields n j (.scalar sc') ++
            [.aggregate 0 (encodeRawAbstractByteVals mergedBytes)])))) s.memory
      stepMirFn body s = .step s' ∧
      ∃ (m' : AnnealStepState) (msc' : Miri.Memory.ScalarInt)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
        (allocId : Miri.Memory.AllocId)
        (la_old : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
          Miri.Memory.MiriMemoryKind)
        (A' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        ScalarRel sc' msc' ∧
        m'.stack.frames = #[tf'] ∧
        tf'.body = translateBody body ∧
        tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ ∧
        tf'.locals.size = body.localDecls.length ∧
        tf'.locals[u]? = some ⟨.live (.indirect mp), some (translateTy uDecl.ty body.layouts)⟩ ∧
        (∀ i decl slot mls, i ≠ u →
          get? body.localDecls i = some decl →
          get? s'.frame.locals i = some slot →
          tf'.locals[i]? = some mls →
          UnionLocalRel m'.machine decl body.layouts slot mls) ∧
        (∀ tf, m.stack.frames = #[tf] → ∀ k,
          IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) ∧
        (allocId, la_old) ∈ m.machine.memory.live.toList ∧
        (allocId, ⟨la_old.kind, A'⟩) ∈ m'.machine.memory.live.toList ∧
        LiveAllocsNodup m'.machine ∧
        IsUnionPrefixMask S sc_old.sizeBytes A'.initializationMask ∧
        A'.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc'.sizeBytes)) false =
            .ok (.fromScalarInt msc') ∧
        (unionAllocRaw A').extract sc'.sizeBytes S =
          (unionAllocRaw la_old.allocation).extract sc'.sizeBytes S ∧
        (f0Ty.kind ≠ .bool → f0Ty.kind ≠ .char →
          UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty
            (unionSpliceLowScalar sc_old sc') mp) ∧
        StepPreservesHighWater m 0 (m', .ok true)) := by
  rcases hstate with
    ⟨topFrame, hframes, _, _, hframe, hcal, _, hbor, hprot, hcaller, hdisj⟩
  have hop_tf := hop topFrame hframes
  have hop_ld := hop_tf.evalOperand_localDecls_eq s.frame.locals s.memory.globals
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot; generalize s.memory = mem; intro hbor hprot
    cases mem; dsimp only at hbor hprot; subst hbor hprot; rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩ body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
  obtain ⟨c_u, hmls_u⟩ := hu_mls topFrame hframes
  obtain ⟨_, mls_u, hlt_af_u, hlt_u, _, hmls_u', hmls_u_eq, hloc_u⟩ := hframe.lookup_local hdecl_u
  rw [hmls_u] at hmls_u'; injection hmls_u' with hmls_u'; subst hmls_u'
  have hcache_u := hloc_u.layout_eq
  cases hmem with
  | mk allocId tag baseAddr la_old msc0 hprov hmis hmeta hlive_old hbase hptr hovf hsz_old hlen_old
      hmut_old hp_old hal_old hex_old hnat_old hk_le0 hmask_old hrel_old hprim0 himm0 hraw_old =>
  have hS := hwt.size_valid
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame u hlt_u layU
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  have hplace : annealEvalUnionFieldPlace body.localDecls body.layouts u j (encodeTyId fty) m =
      .ok ⟨.memory mp, translateTy fty body.layouts⟩ m₀ :=
    annealEvalUnionFieldPlace_indirect hframes hlt_u hdecl_u (by rw [hmls_u_eq]; exact hcache_u)
      (by rw [hmls_u_eq]) hmeta hfields hj hprim
  have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
  have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
      ⟨u, #[.Field j (encodeTyId fty)]⟩ true m =
      .ok ⟨.memory mp, translateTy fty body.layouts⟩ m₀ := by
    show annealEvalPlaceLM2_4 body.localDecls body.layouts ⟨u, #[.Field j (encodeTyId fty)]⟩ m = _
    simp only [annealEvalPlaceLM2_4, hunion, ↓reduceIte]
    exact hplace
  have hframe₀ : FrameRelLM2_4 body m.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_u hlt_u
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ := hdisj.cache_layout hlt_u _
  have hop₀ : WellTypedScalarOperand body topFrame₀ op fty := hop_tf.cache_layout hlt_u layU
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨u, #[.Field j (encodeTyId fty)]⟩
      (translateRvalue (.use op)) = true := by
    simp [lm24Assign, lm24Place, hunion]
  have hm_pre : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
          (some (translateTy fty body.layouts)) >>= fun o =>
          (annealRvalueHooksLM2_4 body.localDecls body.layouts).copyOp () o
            ⟨.memory mp, translateTy fty body.layouts⟩) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateProjectionElem]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace']
    dsimp only [translateRvalue]
    rfl
  have hlm_eq : ∀ st, annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
      (some (translateTy fty body.layouts)) st =
      annealEvalOperand body.localDecls body.layouts (translateOperand op)
        (some (translateTy fty body.layouts)) st := fun st => by
    rw [annealEvalOperandLM2_4_scalar hop₀]
  have hcopy_imm : ∀ (imm : Miri.Interpreter.Immediate AnnealProv)
      (lay : Miri.Interpreter.LocalLayout) (st : AnnealStepState),
      (annealRvalueHooksLM2_4 body.localDecls body.layouts).copyOp () ⟨.immediate imm, lay⟩
          ⟨.memory mp, translateTy fty body.layouts⟩ st =
        (annealReadImmediateLM2_2 ⟨.immediate imm, lay⟩ >>= fun i =>
          annealWriteImmediateLM2_2 i.imm ⟨.memory mp, translateTy fty body.layouts⟩) st := by
    intro imm lay st; rfl
  rcases evalScalarOperand_LM2_4 hframe₀ hprim hop₀ s.memory.globals
      (some (translateTy fty body.layouts)) with
    ⟨ha_ub, ⟨m_err, msg, hm_err⟩ | ⟨lay, st', hm_uninit⟩⟩ |
    ⟨sc', msc', tf₁, ha_ok, hm_ok, hframe₁, hdisj₁, hmono₁, htf₁, hind₁, hrel', himm'⟩
  · refine ⟨fun _ => ?_, fun _ hok => by rw [ha_ub] at hok; cases hok⟩
    have ha : evalStmt s ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue; dsimp only; rw [hbor, hcaller, hop_ld, ha_ub]
    have hm_err' : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        (some (translateTy fty body.layouts)) m₀ = .error (.undefinedBehavior msg) m_err := by
      rw [hlm_eq]; exact hm_err
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩) m =
        (m_err, .error (.undefinedBehavior msg)) := by
      rw [hm_pre]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hm_err']
    rw [hstep_a, ha, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_stmt]
    exact .ub _ _
  · refine ⟨fun _ => ?_, fun _ hok => by rw [ha_ub] at hok; cases hok⟩
    have ha : evalStmt s ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue; dsimp only; rw [hbor, hcaller, hop_ld, ha_ub]
    have hm_uninit' : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        (some (translateTy fty body.layouts)) m₀ = .ok ⟨.immediate .uninit, lay⟩ st' := by
      rw [hlm_eq]; exact hm_uninit
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩) m =
        (st', .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_pre]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hm_uninit', hcopy_imm]; rfl
    rw [hstep_a, ha, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_stmt]
    exact .ub _ _
  · refine ⟨(fun hub => by rw [ha_ok] at hub; cases hub), fun sc_in hok => ?_⟩
    rw [ha_ok] at hok; injection hok with hv _; injection hv with hsc_eq; subst hsc_eq
    intro mergedBytes s'
    cases himm' with
    | scalar _ _ hrel'_sc hsz' hbool' hchar' =>
    have himm' : ImmediateRel fty body.layouts (.scalar sc') (.scalar (.fromScalarInt msc')) :=
      .scalar sc' msc' hrel'_sc hsz' hbool' hchar'
    have hk'_toNat : (translateTy fty body.layouts).layout.size.bytes.toNat = sc'.sizeBytes := by
      rw [hsz']; exact translateSizeBytes_toNat_of_valid hrel'.validBytes
    have hk_lt : sc'.sizeBytes < sc_old.sizeBytes := by rw [← hk'_toNat]; exact hlt_width
    have hk_le_old : sc'.sizeBytes ≤ sc_old.sizeBytes := Nat.le_of_lt hk_lt
    have hk'_le_S : sc'.sizeBytes ≤ S := Nat.le_trans hk_le_old hk_le0
    have hS16 : S ≤ 16 := by rcases hS with h | h | h | h | h <;> omega
    obtain ⟨M', hset_mask, hM'⟩ :=
      hmask_old.setRange_le hS hrel_old.validBytes hrel'.validBytes hk_le_old hk_le0
    obtain ⟨A', hw_alloc, hA'_sz, hA'_len, hA'_align, hA'_mut, hA'_prov, hA'_mask, hA'_extra,
      hA'_native, hA'_raw, hA'_high⟩ :=
      union_writeScalar_prefix_preserve_high hrel' hlen_old hsz_old hS16 hk'_le_S hmut_old hp_old
        hset_mask
    obtain ⟨allocIdx, _, hfindIdx, hget_live, hset_live⟩ :=
      array_findIdx?_of_nodup_fst hnodup hlive_old
    obtain ⟨hnodup', hmem_live', hother⟩ := hset_live ⟨la_old.kind, A'⟩
    have hoff : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = Miri.ABI.Size.ZERO := by
      rw [hptr]; simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
    let mach₃ := inplaceMachine m.machine allocIdx allocId la_old.kind A'
    have hw : annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc'))
        ⟨.memory mp, translateTy fty body.layouts⟩
        { stack := ⟨#[tf₁]⟩, machine := m.machine } =
        .ok () { stack := ⟨#[tf₁]⟩, machine := mach₃ } := by
      rcases la_old with ⟨kind_old, alloc_old⟩
      unfold annealWriteImmediateLM2_2 annealWriteIndirectImmediate
      simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
        stack_currentFrame?_singleton ⟨#[tf₁]⟩ tf₁ rfl, hprov, Option.bind,
        Miri.Memory.Provenance.getAllocId, hbase, add_size_zero_bytes, hoff, hfindIdx, hget_live,
        show (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc').size = msc'.size from rfl,
        hw_alloc, pure, EStateM.pure, set, MonadStateOf.set, EStateM.set]
      rfl
    have hm_ok' : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        (some (translateTy fty body.layouts)) m₀ =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc')), translateTy fty body.layouts⟩
          { stack := ⟨#[tf₁]⟩, machine := m.machine } := by
      rw [hlm_eq]; exact hm_ok
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩) m =
        ({ stack := ⟨#[tf₁]⟩, machine := mach₃ }, .ok ()) := by
      rw [hm_pre]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hm_ok', hcopy_imm]
      simp only [bind, EStateM.bind, annealReadImmediateLM2_2, pure, EStateM.pure]
      rw [hw]
    have htf₁_loc : tf₁.location = topFrame.location := by rw [htf₁]; rfl
    have htf₁_body : tf₁.body = topFrame.body := by rw [htf₁]; rfl
    have hloc₁ : tf₁.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
      rw [htf₁_loc]; exact hframe.location_eq
    have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
      hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl hloc₁
    have hvld := (WellTypedLM2_1ScalarOperand.ofScalar hop_tf).validateLoadedValue_true hbool'
    have hrv : evalRvalue s.frame.locals (.use op) s.memory body.localDecls body.layouts =
        .ok (.scalar sc') s.frame.locals s.memory := by
      unfold evalRvalue; dsimp only; rw [hbor, hcaller, hop_ld, ha_ok]; dsimp only; rw [hvld]
      simp only []
    have hwp := writeProjectedForLocal_union_field_lt (locals := s.frame.locals) hdecl_u hwt
      hfields hf hj hprim0 himm0 hfl0 hprim himm' hk_lt hk_le0 hfl'
    have ha_ok' : evalStmt s ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.step s' := by
      unfold evalStmt; dsimp only; rw [hrv]; simp only []
      rw [hu_slot]; dsimp only
      rw [hwp]; dsimp only
      rw [set?_eq_some_set hlt_af_u, hprot, hbor]
      dsimp only [invalidateConflictingBorrowsAtProj]
      rw [hmem_same]
    have hu₀ : topFrame₀.locals[u]? = some ⟨.live (.indirect mp), some layU⟩ := by
      dsimp only [topFrame₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set_self]; simp [hmls_u_eq]
    have hu₁ : tf₁.locals[u]? = some ⟨.live (.indirect mp), some layU⟩ := by
      rw [hind₁ u mp (some layU) hu₀, hu₀]
    have hdisj₁' := hdisj₁ hdisj₀
    let tf_fin := { tf₁ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
    let m' : AnnealStepState := { stack := ⟨#[tf_fin]⟩, machine := mach₃ }
    have hread_new : A'.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc'.sizeBytes)) false =
          .ok (.fromScalarInt msc') := by
      have hinit_low : A'.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc'.sizeBytes)) =
          .ok (.ok ()) := by
        rw [hA'_mask]
        exact hM'.init hS hrel_old.validBytes hrel'.validBytes hk_le0 hk_le_old
      exact union_readScalar_prefix hrel' hA'_len (hA'_sz.trans hsz_old) hS16 hk'_le_S
        hinit_low hA'_raw
    have hmem_spliced : f0Ty.kind ≠ .bool → f0Ty.kind ≠ .char →
        UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty
          (unionSpliceLowScalar sc_old sc') mp := by
      intro hno_bool hno_char
      have hcan_sp : (unionSpliceLowScalar sc_old sc').bits <
          scalarModulus (unionSpliceLowScalar sc_old sc').sizeBytes :=
        unionSpliceLowScalar_canonical hk_le_old hrel'.canonical hrel_old.canonical
      have hv_sp : ValidScalarBytes (unionSpliceLowScalar sc_old sc').sizeBytes :=
        hrel_old.validBytes
      obtain ⟨msc_sp, _, hrel_sp⟩ := scalarInt_tryFromUInt_of_valid hv_sp hcan_sp
      have hsz0 : (translateTy f0Ty body.layouts).layout.size =
          translateSizeBytes (unionSpliceLowScalar sc_old sc').sizeBytes := by
        cases himm0 with | scalar _ _ _ hsz0 _ _ => exact hsz0
      have himm_sp : ImmediateRel f0Ty body.layouts
          (.scalar (unionSpliceLowScalar sc_old sc')) (.scalar (.fromScalarInt msc_sp)) :=
        .scalar _ msc_sp hrel_sp hsz0
          (fun hb => False.elim (hno_bool hb))
          (fun hc => False.elim (hno_char hc))
      have hraw_sp := allocLeBytes_unionSpliceLowScalar hlen_old hA'_len hk_lt hk_le0
        hrel'.canonical hA'_raw hA'_high hraw_old
      exact .mk allocId tag baseAddr ⟨la_old.kind, A'⟩ msc_sp hprov hmis hmeta hmem_live' hbase
        hptr hovf (hA'_sz.trans hsz_old) hA'_len hA'_mut hA'_prov (hA'_align.trans hal_old)
        (hA'_extra.trans hex_old) (hA'_native.trans hnat_old) hk_le0 (hA'_mask ▸ hM') hrel_sp
        hprim0 himm_sp hraw_sp
    refine ⟨by rw [hstep_a, ha_ok'], m', msc', tf_fin, allocId, la_old, A', hstep_m, hrel', rfl,
      by show tf₁.body = _; rw [htf₁_body]; exact hframe.body_eq,
      rfl, hframe₁.mf_locals_size, hu₁, ?_, ?_, hlive_old, hmem_live', hnodup', hA'_mask ▸ hM',
      hread_new, hA'_high, hmem_spliced, ?_⟩
    · intro i decl slot mls hne hdecl hslot hmls
      have hslot' : get? s.frame.locals i = some slot := by
        dsimp only [s', advanceStmt] at hslot
        rwa [get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hne), ← get?_eq_getElem?] at hslot
      have hloc := hframe₁.locals_rel i decl slot mls hdecl hslot' hmls
      refine hloc.of_entry ?_
      intro mp_i c_i hmi a la hpa hla
      subst hmi
      have hne_a : a ≠ allocId := by
        intro hae
        rw [hae] at hpa
        have := hdisj₁' u i mp mp_i (some layU) c_i (Ne.symm hne) hu₁ hmls
        rw [show mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some allocId by
              rw [hprov]; rfl, hpa] at this
        exact this rfl
      exact ⟨hother a la hne_a hla, rfl⟩
    · intro tf htf k himm_k
      rw [hframes] at htf
      have htf' : topFrame = tf := by simpa using htf
      subst htf'
      exact hmono₁ k (himm_k.cache_layout hlt_u layU)
    · intro _ hw0 _
      obtain ⟨hw', hnext⟩ := MemoryHighWater.inplaceMachine (kind := la_old.kind) (alloc := A')
        (allocIdx := allocIdx) hw0 hlive_old
      exact ⟨hw', by rw [hnext]; omega⟩

/-- Step `r = copy/move (_u.j : f0Ty)` in `lean-miri` directly from `UnionMemRel`
for `(f0Ty, sc)` on `_u` (applicable even when Anneal's `_u` carries a `D13a`
raw-byte overlay after `step_union_narrower_field_write_correspondence`). -/
theorem miri_step_union_field_read_of_unionMemRel
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hnodup : LiveAllocsNodup m.machine)
    (hframes : m.stack.frames = #[topFrame])
    {blockIdx stmtIdx : Nat}
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hsize : topFrame.locals.size = body.localDecls.length)
    {bb : BasicBlockData} {r u j : Local} {f0Ty : Ty} {isMove : Bool} {span : String}
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hstmt : get? bb.statements stmtIdx =
      some ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j f0Ty)), span⟩)
    {rDecl uDecl : LocalDecl}
    (hdecl_r : get? body.localDecls r = some rDecl)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (_hr_ty : rDecl.ty = f0Ty)
    {S n : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hj : j < n)
    {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_mls : topFrame.locals[u]? = some ⟨.live (.indirect mp),
      some (translateTy uDecl.ty body.layouts)⟩)
    {slot_r : LocalSlot}
    (hr_live : slot_r ≠ .dead)
    (hr_rel : ∀ mls, topFrame.locals[r]? = some mls →
      UnionLocalRel m.machine rDecl body.layouts slot_r mls)
    (hr_imm : IsImmediateFrameLocal topFrame r)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp) :
    ∃ (m' : AnnealStepState)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (msc : Miri.Memory.ScalarInt),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      ScalarRel sc msc ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c, tf'.locals[r]? = some ⟨.live (.immediate (.scalar (.fromScalarInt msc))), c⟩) := by
  have hlt_r0 : r < topFrame.locals.size := by
    rw [get?_eq_getElem?] at hdecl_r
    rw [hsize]; exact (List.getElem?_eq_some_iff.mp hdecl_r).1
  have hlt_u0 : u < topFrame.locals.size := by
    rw [get?_eq_getElem?] at hdecl_u
    rw [hsize]; exact (List.getElem?_eq_some_iff.mp hdecl_u).1
  have hmls_r0 : topFrame.locals[r]? = some (topFrame.locals[r]'hlt_r0) :=
    Array.getElem?_eq_getElem hlt_r0
  have hloc_r0 := hr_rel _ hmls_r0
  have hru : r ≠ u := fun hru => by subst hru; exact hr_imm _ hu_mls mp rfl
  let topFrame₀ :=
    cacheFrameLocalLayout topFrame r hlt_r0 (translateTy rDecl.ty body.layouts)
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 r none topFrame.localsIdentity, translateTy rDecl.ty body.layouts⟩
  have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨r, #[]⟩ m =
      .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_r0 hdecl_r hloc_r0.layout_eq
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀, cacheFrameLocalLayout]; rw [Array.size_set]; exact hlt_u0
  have hu₀' : topFrame₀.locals[u]? =
      some ⟨.live (.indirect mp), some (translateTy uDecl.ty body.layouts)⟩ := by
    dsimp only [topFrame₀, cacheFrameLocalLayout]
    rw [Array.getElem?_set_ne _ hru]; exact hu_mls
  have hu₀ : topFrame₀.locals[u]'hlt_u₀ =
      ⟨.live (.indirect mp), some (translateTy uDecl.ty body.layouts)⟩ := by
    have h := Array.getElem?_eq_getElem hlt_u₀
    rw [hu₀'] at h; exact (Option.some.inj h).symm
  have hcache_u : ∀ l, (topFrame₀.locals[u]'hlt_u₀).layout = some l →
      l = translateTy uDecl.ty body.layouts := by
    rw [hu₀]; intro l hl; exact (Option.some.inj hl).symm
  obtain ⟨hmeta, hprim0⟩ : mp.metadata = .none ∧ IsPrimScalarTy f0Ty := by
    cases hmem with
    | mk _ _ _ _ _ _ _ hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp0 _ _ => exact ⟨hm, hp0⟩
  let topFrame₁ :=
    cacheFrameLocalLayout topFrame₀ u hlt_u₀ (translateTy uDecl.ty body.layouts)
  let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
  have hop : annealEvalOperandLM2_4 body.localDecls body.layouts
      (translateOperand (unionFieldReadOperand isMove u j f0Ty))
      (some (translateTy rDecl.ty body.layouts)) m₀ =
      .ok ⟨.indirect mp, translateTy f0Ty body.layouts⟩ m₁ := by
    have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
    have hfield := annealEvalUnionField_indirect (body := body) (m := m₀) rfl hlt_u₀ hdecl_u
      hcache_u (by rw [hu₀]) hmeta hfields hj hprim0
    cases isMove <;>
      simp only [unionFieldReadOperand, translateOperand, translatePlace, List.map,
        translateProjectionElem, List.toArray, annealEvalOperandLM2_4, hunion, ↓reduceIte,
        Bool.false_eq_true] <;>
      exact hfield
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨r, #[]⟩
      (translateRvalue (.use (unionFieldReadOperand isMove u j f0Ty))) = true := by
    have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
    cases isMove <;>
      simp [lm24Assign, lm24Rvalue, lm24Operand, lm24Place, translateRvalue, translateOperand,
        unionFieldReadOperand, translatePlace, hunion]
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j f0Ty)), span⟩) m =
      Miri.Interpreter.runRvalue
        ((annealReadImmediateLM2_2 ⟨.indirect mp, translateTy f0Ty body.layouts⟩ >>=
          fun imm => annealWriteImmediateLM2_2 imm.imm destPlace)) m₁ := by
    have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
        ⟨r, #[]⟩ true m = .ok destPlace m₀ := hevalPlace_dst
    have hop' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
        (Miri.Interpreter.OperandPath.rvalue "operand")
        (translateOperand (unionFieldReadOperand isMove u j f0Ty))
        (some ((annealRvalueHooksLM2_4 body.localDecls body.layouts).placeLayout destPlace)) m₀ =
        .ok ⟨.indirect mp, translateTy f0Ty body.layouts⟩ m₁ := hop
    have huse : usesMemCopy ⟨.indirect mp, translateTy f0Ty body.layouts⟩ = false := by
      simp [usesMemCopy, hprim0.fields_primitive]
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace']
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop']
    simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2, huse, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨hf0sz, hkv⟩ := hmem.f0_size
  obtain ⟨hsame, _⟩ := annealReadImmediate_unionMem (m := m₁) hnodup hwt.size_valid hmem
    hprim0 hkv hf0sz
  obtain ⟨msc, hrel_sc, _, hread⟩ := hsame rfl
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j f0Ty)), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc)) destPlace) m₁ := by
    rw [hm_eval]
    apply runRvalue_eq_of_eq
    exact EStateM.bind_eq_ok hread
  have hlt_r₁ : r < topFrame₁.locals.size := by
    dsimp only [topFrame₁, cacheFrameLocalLayout]
    rw [Array.size_set]
    dsimp only [topFrame₀, cacheFrameLocalLayout]
    rw [Array.size_set]; exact hlt_r0
  have hr_imm₁ : IsImmediateFrameLocal topFrame₁ r :=
    (hr_imm.cache_layout hlt_r0 _).cache_layout hlt_u₀ _
  have hmls_r₁ : topFrame₁.locals[r]? = some (topFrame₁.locals[r]'hlt_r₁) :=
    Array.getElem?_eq_getElem hlt_r₁
  have hget_r₁ := frame_getLocal_of_getElem? topFrame₁ r _ hmls_r₁
  have hmls_r₁_val : ∃ imm_old c_old,
      topFrame₁.locals[r]'hlt_r₁ = ⟨.live (.immediate imm_old), c_old⟩ := by
    have hr₁_eq : topFrame₁.locals[r]? =
        some { topFrame.locals[r]'hlt_r0 with layout := some (translateTy rDecl.ty body.layouts) } := by
      dsimp only [topFrame₁, cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ hru.symm]
      dsimp only [topFrame₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set_self]
    rw [hr₁_eq] at hmls_r₁
    have h_eq := (Option.some.inj hmls_r₁).symm
    rcases hm_r0 : topFrame.locals[r]'hlt_r0 with ⟨vr, cr⟩
    rw [hm_r0] at hloc_r0 h_eq
    cases vr with
    | dead =>
      cases hloc_r0 with
      | base _ _ hl =>
        cases hl
        exact False.elim (hr_live rfl)
    | live op_r =>
      cases op_r with
      | indirect mp_r =>
        rw [hm_r0] at hmls_r0
        exact False.elim (hr_imm _ hmls_r0 mp_r rfl)
      | immediate imm_old =>
        exact ⟨imm_old, _, h_eq⟩
  obtain ⟨imm_old, c_old, h_r₁_eq⟩ := hmls_r₁_val
  rw [h_r₁_eq] at hget_r₁
  let topFrame₂ :=
    { topFrame₁ with
      locals := topFrame₁.locals.set r
        { topFrame₁.locals[r]'hlt_r₁ with
          value := .live (.immediate (.scalar (.fromScalarInt msc))) } hlt_r₁ }
  have hm_ok : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j f0Ty)), span⟩) m =
      ({ m with stack := ⟨#[topFrame₂]⟩ }, .ok ()) := by
    rw [hm_write]
    unfold Miri.Interpreter.runRvalue
    dsimp only [destPlace]
    have hid_eq : topFrame.localsIdentity = topFrame₁.localsIdentity := rfl
    rw [hid_eq, annealWriteImmediateLM2_2_live (topFrame := topFrame₁) rfl hlt_r₁ hget_r₁]
  have hloc₂ : topFrame₂.location = .mir ⟨blockIdx, stmtIdx⟩ := hloc
  have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
    hframes hbody hloc hbb hstmt hm_ok rfl hloc₂
  refine ⟨_, _, msc, hstep_m, hrel_sc, rfl, ⟨(topFrame₁.locals[r]'hlt_r₁).layout, ?_⟩⟩
  dsimp only [topFrame₂]
  rw [Array.getElem?_set_self]

/-! ## 14. Zero-Sized Indirect Uninitialized Array `Subslice` Characterization

`MemPlaceRel`'s `uninit_consistent` clause constrains the initialization mask
only when the type's byte size is nonzero (`Relation.lean`). For a `0`-element
array `[T; 0]` that Anneal holds as `.uninit` while `lean-miri` holds as
`.live (.indirect mp)`, Anneal always reports `.ub`, whereas
`annealEvalSubsliceOperand` calls `InitMask.isRangeInitialized` on the empty
range `[relOffset, relOffset + 0)`:

1. When `localAlloc.allocation.initializationMask.blocks = .Lazy false` (such as
   a fresh allocation created by `forceAllocation`), `isRangeInitialized`
   returns `.error` / `.ok (.error _)`, so **both** Anneal and `lean-miri`
   report undefined behavior.
2. When `localAlloc.allocation.initializationMask = InitMask.new byteSize true`
   (such as a `[T; 0]` allocation that was previously initialized and later
   `writeUninit`ed, since `writeUninit` is a no-op on `0` bytes),
   `isRangeInitialized` returns `.ok (.ok ())`, so `lean-miri` succeeds on
   `a[0..0]` while Anneal reports `.ub`. -/

private theorem isRangeInitialized_lazy_false_ne_ok {mask : Miri.Memory.InitMask}
    (hlazy : mask.blocks = .Lazy false) (range : Miri.Memory.AllocRange) :
    mask.isRangeInitialized range ≠ .ok (.ok ()) := by
  unfold Miri.Memory.InitMask.isRangeInitialized
  rw [hlazy]
  cases range.endExclusive with
  | error _ => intro h; cases h
  | ok finish =>
    dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    split
    · cases Miri.Memory.AllocRange.fromEndpoints mask.len finish <;> intro h <;> cases h
    · intro h; cases h

/-- **`evalSubsliceOperand_zero_uninit_indirect_characterization`** (`LM-2.4`):
exact mask-representation split for `copy/move a[fromIdx..toIdx]` on a
`0`-element memory-backed array `[T; 0]` that Anneal holds as `.uninit`. -/
theorem evalSubsliceOperand_zero_uninit_indirect_characterization
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hstate : StateRelLM2_4 body s m)
    (hframes : m.stack.frames = #[topFrame])
    (hnodup : LiveAllocsNodup m.machine)
    {arrIdx : Local} {arrDecl : LocalDecl} {elemKind : RigidTy}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind 0)
    (huninit : get? s.frame.locals arrIdx = some .uninit)
    {mp : Miri.Interpreter.MemPlace AnnealProv} {c : Option Miri.Interpreter.LocalLayout}
    (hind : topFrame.locals[arrIdx]? = some ⟨.live (.indirect mp), c⟩) :
    ∃ (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag)
      (localAlloc : Miri.Memory.LocalAllocation AnnealProv
        (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind)
      (topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      (allocId, localAlloc) ∈ m.machine.memory.live.toList ∧
      StateRelLM2_4 body s { m with stack := ⟨#[topFrame']⟩ } ∧
      (localAlloc.allocation.initializationMask.blocks = .Lazy false →
        ∀ isMove fromIdx toIdx fromEnd known,
          let op := subsliceReadOperand isMove arrIdx fromIdx toIdx fromEnd
          evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil body.localDecls =
            .ub ∧
          annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) known m =
            .error (.undefinedBehavior "access to uninitialized indirect place")
              { m with stack := ⟨#[topFrame']⟩ }) ∧
      (localAlloc.allocation.initializationMask =
          Miri.Memory.InitMask.new localAlloc.allocation.byteSize true →
        ∀ isMove fromEnd known,
          let op := subsliceReadOperand isMove arrIdx 0 0 fromEnd
          let arrLay := translateTy arrDecl.ty body.layouts
          let es := (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size
          evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil body.localDecls =
            .ub ∧
          annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) known m =
            .ok ⟨.indirect mp,
                 { ty := arrLay.ty,
                   layout := { arrLay.layout with
                     fields := .Array es 0,
                     size := Miri.ABI.Size.ZERO } }⟩
              { m with stack := ⟨#[topFrame']⟩ }) := by
  rcases hstate with
    ⟨tf_s, hframes_s, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have htf_eq : tf_s = topFrame := by
    rw [hframes] at hframes_s
    simpa using hframes_s.symm
  rw [htf_eq] at hretCont hretPlace hframe hdisj
  clear hframes_s htf_eq tf_s
  obtain ⟨slot_arr, mls_arr, _, hlt_arr, hslot_arr, hmls_arr, hmls_arr_eq, hloc_arr⟩ :=
    hframe.lookup_local hdecl_arr
  rw [huninit] at hslot_arr
  injection hslot_arr with hslot_arr
  subst hslot_arr
  rw [hind] at hmls_arr
  injection hmls_arr with hmls_arr
  subst hmls_arr
  have hmp : MemPlaceRel m.machine arrDecl.ty body.layouts none mp := by
    cases hloc_arr with
    | base _ _ hl =>
      cases hl with
      | indirect _ _ _ _ _ hmp => exact hmp
  let arrLay := translateTy arrDecl.ty body.layouts
  let topFrame' :=
    cacheFrameLocalLayout topFrame arrIdx hlt_arr (translateTy arrDecl.ty body.layouts)
  let m' : AnnealStepState := { m with stack := ⟨#[topFrame']⟩ }
  have hcache_arr : ∀ l, (topFrame.locals[arrIdx]'hlt_arr).layout = some l →
      l = translateTy arrDecl.ty body.layouts := by
    rw [hmls_arr_eq]; exact hloc_arr.layout_eq
  have hframe' : FrameRelLM2_4 body m.machine s.frame topFrame' :=
    hframe.cache_local_layout hdecl_arr hlt_arr
  have hdisj' : MemoryAllocDisjoint topFrame' := hdisj.cache_layout hlt_arr _
  have hstate' : StateRelLM2_4 body s m' :=
    StateRelLM2_4.mk topFrame' rfl hretCont ⟨retLay, hretPlace⟩ hframe' hcal hstack hbor hprot
      hcaller hdisj'
  have hlt_arr' : arrIdx < topFrame'.locals.size := by
    unfold topFrame' cacheFrameLocalLayout; simp [hlt_arr]
  have hval_arr' : (topFrame'.locals[arrIdx]'hlt_arr').value = .live (.indirect mp) := by
    dsimp only [topFrame', cacheFrameLocalLayout]
    simp only [Array.getElem_set_self, hmls_arr_eq]
  have hgop : topFrame'.getLocalOperand arrIdx = .ok (.indirect mp) := by
    unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
      Miri.Interpreter.LocalState.access
    simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
  have hnot_empty : m.stack.currentFrame?.isNone = false := by
    rw [stack_currentFrame?_singleton m.stack topFrame hframes]; rfl
  have harr_sz0 : arrLay.layout.size = Miri.ABI.Size.ZERO := by
    dsimp only [arrLay]
    rw [hwf.arr_size]
    simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
  cases hmp with
  | mk allocId tag baseAddr relOffset localAlloc hprov _ hmeta hlive hbase _ hptr _ _ hbounds
      _ _ _ _ =>
    have hfind := array_find?_of_nodup_fst hnodup hlive
    have hrel_sz : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = relOffset := by
      have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
      rw [hbytes, uint64_add_sub_cancel_left]; cases relOffset; rfl
    refine ⟨allocId, tag, localAlloc, topFrame', hprov, hlive, hstate', ?_, ?_⟩
    · intro hlazy isMove fromIdx toIdx fromEnd known
      dsimp only
      have ha_ub : evalOperand s.frame.locals
          (subsliceReadOperand isMove arrIdx fromIdx toIdx fromEnd) .nil s.memory.globals
          body.layouts .nil body.localDecls = .ub := by
        cases isMove <;> simp [subsliceReadOperand, evalOperand, huninit]
      have hres_arr := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt_arr
        hdecl_arr hcache_arr
      have hne_ok := isRangeInitialized_lazy_false_ne_ok hlazy
        (Miri.Memory.allocRange relOffset arrLay.layout.size)
      have hchk_err : annealCheckIndirectInitialized m.machine mp arrLay.layout.size =
          .error (.undefinedBehavior "access to uninitialized indirect place") := by
        unfold annealCheckIndirectInitialized
        rw [hprov]
        simp only [Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind, hrel_sz]
        cases hmask : localAlloc.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange relOffset arrLay.layout.size) with
        | error _ => rfl
        | ok inner =>
          cases inner with
          | error _ => rfl
          | ok u => cases u; exact absurd hmask hne_ok
      refine ⟨ha_ub, ?_⟩
      dsimp only [arrLay] at hchk_err
      dsimp only [topFrame'] at hgop ⊢
      rw [annealEvalOperandLM2_4_subslice]
      unfold annealEvalSubsliceOperand
      simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure,
        EStateM.pure, hnot_empty, hres_arr, hgop, hchk_err, throw, throwThe, MonadExceptOf.throw,
        EStateM.throw]
    · intro hmask_true isMove fromEnd known
      dsimp only
      have ha_ub : evalOperand s.frame.locals (subsliceReadOperand isMove arrIdx 0 0 fromEnd)
          .nil s.memory.globals body.layouts .nil body.localDecls = .ub := by
        cases isMove <;> simp [subsliceReadOperand, evalOperand, huninit]
      have hres_arr := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt_arr
        hdecl_arr hcache_arr
      have hend0 : (Miri.Memory.allocRange relOffset Miri.ABI.Size.ZERO).endExclusive =
          .ok relOffset := by
        have hlt0 : relOffset.bytes.toNat + Miri.ABI.Size.ZERO.bytes.toNat < 2 ^ 64 := by
          simp [Miri.ABI.Size.ZERO]; exact UInt64.toNat_lt _
        have h := allocRange_endExclusive_of_lt (off := relOffset) (sz := Miri.ABI.Size.ZERO) hlt0
        simpa [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes] using h
      have hchk_ok : annealCheckIndirectInitialized m.machine mp arrLay.layout.size = .ok () := by
        unfold annealCheckIndirectInitialized
        rw [hprov, harr_sz0]
        simp only [Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind, hrel_sz,
          hmask_true]
        have hinit0 : (Miri.Memory.InitMask.new localAlloc.allocation.byteSize true).isRangeInitialized
            (Miri.Memory.allocRange relOffset Miri.ABI.Size.ZERO) = .ok (.ok ()) := by
          apply Miri.Memory.InitMask.lazy_initialized_query _ _ _ hend0
          rw [UInt64.le_iff_toNat_le]
          omega
        rw [hinit0]
        rfl
      let es := (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size
      let cx := annealSubsliceProjectionCx topFrame' body.layouts m.machine
      let base : Miri.Interpreter.OpTy AnnealProv := ⟨.indirect mp, arrLay⟩
      have hfields : base.layout.layout.fields = .Array es 0 := hwf.arr_fields
      have hisSized : base.layout.layout.isSized = true := hwf.arr_isSized
      have hlen : base.len cx = .ok 0 := by
        unfold Miri.Interpreter.OpTy.len
        rw [hisSized, hfields]; rfl
      have hmul0 : es.mul 0 = .ok Miri.ABI.Size.ZERO := by
        simp [Miri.ABI.Size.mul, Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
      have hsublay0 : cx.subsliceLayout base.layout 0 =
          .ok ({ ty := arrLay.ty,
                 layout := { arrLay.layout with
                   fields := .Array es 0,
                   size := Miri.ABI.Size.ZERO } }, .none) := by
        show annealSubsliceLayout arrLay 0 = _
        unfold annealSubsliceLayout
        have hf : arrLay.layout.fields = .Array es 0 := hwf.arr_fields
        simp [hf, hmul0]
      have hpl0 : annealProjectList cx base [.Subslice 0 0 fromEnd] =
          .ok ⟨.indirect mp,
               { ty := arrLay.ty,
                 layout := { arrLay.layout with
                   fields := .Array es 0,
                   size := Miri.ABI.Size.ZERO } }⟩ := by
        have hnot_ge64 : ¬((0 : Nat) ≥ 2 ^ 64 || (0 : Nat) ≥ 2 ^ 64) := by decide
        simp only [annealProjectList, Miri.Interpreter.project, hnot_ge64]
        change (do
          let next ← Miri.Interpreter.projectSubslice cx base 0 0 fromEnd
          Except.ok next) = _
        unfold Miri.Interpreter.projectSubslice Miri.Interpreter.prepareSubslice
        rw [hlen, hfields]
        cases fromEnd
        · have hnot_lt0 : ¬((0 : UInt64) < 0) := by decide
          have hsub0 : (0 : UInt64) - 0 = 0 := rfl
          simp only [Bool.false_eq_true, ↓reduceIte, hmul0, Except.mapError, hnot_lt0,
            bind, Except.bind, pure, Except.pure, hsub0, hsublay0]
          unfold Miri.Interpreter.OpTy.offsetWithMeta
          simp only [cx, base, annealSubsliceProjectionCx, annealProjectionCx, bind, Except.bind,
            pure, Except.pure, projectionMemoryOffset_zero, memPlace_offset_zero_eq mp hmeta]
        · have hnot_oob0 : ¬((0 : UInt64).toNat + (0 : UInt64).toNat ≥ 2 ^ 64 ||
              (0 : UInt64).toNat + (0 : UInt64).toNat > (0 : UInt64).toNat) := by decide
          have hnot_lt0 : ¬((0 : UInt64) - 0 < 0) := by decide
          have hsub0 : (0 : UInt64) - 0 - 0 = 0 := rfl
          simp only [↓reduceIte, hnot_oob0, Bool.false_eq_true, hmul0, Except.mapError, hnot_lt0,
            bind, Except.bind, pure, Except.pure, hsub0, hsublay0]
          unfold Miri.Interpreter.OpTy.offsetWithMeta
          simp only [cx, base, annealSubsliceProjectionCx, annealProjectionCx, bind, Except.bind,
            pure, Except.pure, projectionMemoryOffset_zero, memPlace_offset_zero_eq mp hmeta]
      refine ⟨ha_ub, ?_⟩
      dsimp only [arrLay, cx, base, topFrame', es] at hchk_ok hpl0 hgop ⊢
      rw [annealEvalOperandLM2_4_subslice]
      unfold annealEvalSubsliceOperand
      simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
        hnot_empty, hres_arr, hgop, hchk_ok, hpl0, pure, EStateM.pure]

/-! ## 15. Statement-Level `Subslice` Assignment Simulation

`step_subslice_assign_simulation` lifts `evalSubsliceOperand_simulation` and
`annealMemCopyOp` to the full statement `_d = copy/move a[fromIdx..toIdx]` on
`StateRelLM2_4`-related states, covering dead/uninitialized UB, `fromEnd = true`
out-of-bounds UB, and in-bounds sub-array extraction (for both empty `cnt = 0`
and non-empty `0 < cnt` subslices, preserving `a` even when `isMove = true`). -/

/-- `annealMemCopyOp` from an `ArraySliceRel` subslice `subMp` (at offset
`srcOff` of live allocation `allocId`) into an uninitialized immediate array
local `d` of type `[elemKind; cnt]`: `d` moves into the fresh allocation `id`,
which is populated either by canonicalizing `[elemKind; 0]` (`cnt = 0`) or by
running `Miri.Memory.Allocation.copy` (`0 < cnt`), yielding `ArraySliceRel` at
offset `0`. -/
theorem annealMemCopyOp_freshArray
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {d : Nat} {dDecl : LocalDecl} {elemKind : RigidTy} {cnt : Nat}
    (hlt : d < tf.locals.size)
    (hdecl : get? body.localDecls d = some dDecl)
    (hwf_d : WellTypedArrayTy body.layouts dDecl.ty elemKind cnt)
    (hc : (tf.locals[d]'hlt).layout = some (translateTy dDecl.ty body.layouts))
    (hval : (tf.locals[d]'hlt).value = .live (.immediate .uninit))
    {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id))
    (hnodup : LiveAllocsNodup m.machine)
    {subMp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag}
    {baseAddr : UInt64} {srcOff : Miri.ABI.Size}
    {la : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    {sub : List Value}
    (hprov : subMp.ptr.provenance = some (.concrete allocId tag))
    (hlive : (allocId, la) ∈ m.machine.memory.live.toList)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hsrcOff : Miri.ABI.Size.ofBytes (subMp.ptr.offset.bytes - baseAddr) = srcOff)
    (hslice : ArraySliceRel elemKind cnt body.layouts sub srcOff la.allocation)
    (srcLay : Miri.Interpreter.LocalLayout) (ident : Miri.Interpreter.LocalsIdentity) :
    ∃ dest' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      annealMemCopyOp body.localDecls body.layouts ⟨.indirect subMp, srcLay⟩
          ⟨.local 0 d none ident, translateTy dDecl.ty body.layouts⟩ m =
        .ok () { stack := ⟨#[setFrameLocalIndirect tf d hlt (stackAllocPlace id)]⟩,
                 machine := stackAllocMachine m.machine mem' id dest' } ∧
      dest'.byteSize = (translateTy dDecl.ty body.layouts).layout.size ∧
      ArraySliceRel elemKind cnt body.layouts sub Miri.ABI.Size.ZERO dest' := by
  let layD := translateTy dDecl.ty body.layouts
  obtain ⟨alloc, htry, hbs, hlen, _, hmut, hal, hprov_alloc, hmask_alloc⟩ :=
    freshUnionAlloc_spec layD.layout.size layD.layout.align.abi
      (translateTy_align_pow2_le_29 dDecl.ty body.layouts)
  have hraw_alloc := tryNew_uninit_raw layD.layout.size layD.layout.align.abi alloc htry
  have hcf := cacheFrameLocalLayout_of_cached tf hlt hc
  have hlt' : d < (cacheFrameLocalLayout tf d hlt layD).locals.size := by rw [hcf]; exact hlt
  have hforce := annealForceUnionAllocation_of_ok (forceAllocation_uninit_eq (body := body) hframes hlt
    hdecl (fun l hl => by rw [hc] at hl; exact (Option.some.inj hl).symm) hval hwf_d.arr_isSized
    htry hres ident layD hlt')
  rw [setFrameLocalIndirect_congr hcf hlt' hlt] at hforce
  obtain ⟨hlive_b, hfreshne, hbase_b⟩ :=
    stackAllocMachine_live_base (mach := m.machine) (alloc.withExtra none) hres
  have hne : allocId ≠ id := hfreshne allocId la hlive
  have hnodup₂ := LiveAllocsNodup.stackAllocMachine (alloc.withExtra none) hnodup hres
  have hfind := array_find?_of_nodup_fst hnodup₂ (hlive_b _ hlive)
  have hbase₂ : (stackAllocMachine m.machine mem' id (alloc.withExtra none)).lookupBaseAddr
      allocId = some baseAddr := by
    rw [hbase_b _ _ hlive]; exact hbase
  have hbase_id := lookupBaseAddr_stackAllocMachine_self m.machine mem' id (alloc.withExtra none)
  have hfresh : mem'.live.any (fun entry => entry.1 == id) = false := by
    have h := (reserveAllocId_ok_live hres).2
    rwa [← (reserveAllocId_ok_live hres).1] at h
  have hidx := findIdx?_push_fresh mem'.live id
    ({ kind := .stack, allocation := alloc.withExtra none } : Miri.Memory.LocalAllocation
      AnnealProv (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind) hfresh
  have hlive₂ : (stackAllocMachine m.machine mem' id (alloc.withExtra none)).memory.live =
      mem'.live.push (id, ⟨.stack, alloc.withExtra none⟩) := rfl
  have hfind' : (mem'.live.push (id, ⟨.stack, alloc.withExtra none⟩)).find?
      (fun x => x.fst == allocId) = some (allocId, la) := hfind
  have hdestOff : Miri.ABI.Size.ofBytes
      ((Miri.ABI.Size.ofBytes (annealStackBaseAddr id)).bytes - annealStackBaseAddr id) =
      Miri.ABI.Size.ZERO := by
    simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
  have hbeqf : (allocId == id) = false := beq_false_of_ne hne
  rcases Nat.eq_zero_or_pos cnt with rfl | hpos
  · have hsub_nil : sub = [] := List.eq_nil_of_length_eq_zero hslice.elems_len
    subst hsub_nil
    have hsz0 : layD.layout.size = Miri.ABI.Size.ZERO := by
      dsimp only [layD]; rw [hwf_d.arr_size]; simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
    have hsz_beq : (layD.layout.size.bytes == 0) = true := by rw [hsz0]; rfl
    have hd_bs_beq : ((alloc.withExtra
        (none : Option Miri.TreeBorrows.BorrowTree)).byteSize.bytes == 0) = true := by
      show (alloc.byteSize.bytes == 0) = true
      rw [hbs, hsz0]; rfl
    have hgb_src := getBytesUnchecked_at (A := la.allocation) srcOff layD.layout.size
      hslice.alloc_len (by rw [hsz0]; simpa [Miri.ABI.Size.ZERO] using hslice.slice_in_bounds)
    have hgb_dst := getBytesUnchecked_at
      (A := alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)) Miri.ABI.Size.ZERO
      layD.layout.size (by show alloc.len = alloc.byteSize.bytes.toNat; rw [hlen, hbs])
      (by show 0 + layD.layout.size.bytes.toNat ≤ alloc.byteSize.bytes.toNat; rw [hbs]; simp)
    have hmut_bne : ((alloc.withExtra
        (none : Option Miri.TreeBorrows.BorrowTree)).mutability != .Mut) = false := by
      show (alloc.mutability != .Mut) = false
      rw [hmut]; rfl
    obtain ⟨zeroAlloc, hfb, hdest_sz, _, _, _, _, _, _, _, hslice0⟩ :=
      zero_array_fromBytes_spec elemKind body.layouts
        (align := (alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)).align)
        (by show alloc.align.pow2 ≤ 29; rw [hal]
            exact translateTy_align_pow2_le_29 dDecl.ty body.layouts)
        none
    refine ⟨zeroAlloc.withExtra none, ?_, hdest_sz.trans hsz0.symm, hslice0⟩
    unfold annealMemCopyOp
    simp only [layD] at hforce hsz_beq hgb_src hgb_dst ⊢
    simp only [bind, EStateM.bind, hforce, get, getThe, MonadStateOf.get, EStateM.get, hprov,
      Option.bind, Miri.Memory.Provenance.getAllocId, hbase₂, stackAllocPlace, hbase_id,
      hlive₂, hfind', hidx, Array.getElem?_push_size, hsrcOff, hdestOff, hsz_beq, ↓reduceIte,
      hgb_src, hgb_dst, hmut_bne, Bool.false_eq_true, hd_bs_beq, hfb, set, MonadStateOf.set,
      array_push_set!_size]
    rfl
  · have htot_pos : 0 < cnt *
        (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat :=
      Nat.mul_pos hpos hwf_d.elem_size_pos
    have hsz_nz : (layD.layout.size.bytes == 0) = false := by
      cases h0 : (layD.layout.size.bytes == 0) with
      | false => rfl
      | true =>
        have := eq_of_beq h0
        have htn : layD.layout.size.bytes.toNat = 0 := by rw [this]; rfl
        dsimp only [layD] at htn
        rw [hwf_d.arr_size_toNat] at htn
        omega
    obtain ⟨dest', hcopy, hsz', _, _, _, _, _, _, _, hslice'⟩ :=
      array_copy_freshAlloc_spec hslice hpos hwf_d.elem_size_pos
        (dest := alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree))
        (by show unionAllocRaw alloc = _; rw [hraw_alloc]; dsimp only [layD]; rw [hwf_d.arr_size_toNat])
        (by show alloc.byteSize = _; rw [hbs]; exact hwf_d.arr_size)
        hmut hprov_alloc
        (by show alloc.initializationMask = Miri.Memory.InitMask.new alloc.byteSize false
            rw [hmask_alloc, hbs])
    have hcopy' : Miri.Memory.Allocation.copy la.allocation
        (Miri.Memory.allocRange srcOff layD.layout.size)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true (alloc.withExtra none) =
          .ok () dest' := by
      dsimp only [layD]
      rw [hwf_d.arr_size]
      exact hcopy
    refine ⟨dest', ?_, hsz'.trans hwf_d.arr_size.symm, hslice'⟩
    unfold annealMemCopyOp
    simp only [layD] at hforce hsz_nz hcopy' ⊢
    simp only [bind, EStateM.bind, hforce, get, getThe, MonadStateOf.get, EStateM.get, hprov,
      Option.bind, Miri.Memory.Provenance.getAllocId, hbase₂, stackAllocPlace, hbase_id,
      hlive₂, hfind', hidx, Array.getElem?_push_size, hsrcOff, hdestOff, hsz_nz,
      Bool.false_eq_true, ↓reduceIte, hbeqf, hcopy', set, MonadStateOf.set, array_push_set!_size]
    rfl

/-- **`step_subslice_assign_simulation`** (`LM-2.4`): statement-level simulation
for `_d = copy a[fromIdx..toIdx]` (or `move a[fromIdx..toIdx]`) assigning a
`Subslice` of a `count`-element array local `a` into an uninitialized immediate
array local `_d` of length `cnt = subsliceEnd count toIdx fromEnd - fromIdx` on
`StateRelLM2_4`-related states:

1. If `a` is dead, or `a` is uninitialized (`0 < count` or immediate), both
   machines report undefined behavior (`StepRelLM2_4.ub`).
2. If `a` is initialized and `fromEnd = true` with
   `count < fromIdx + toIdx < 2 ^ 64`, both machines report undefined behavior
   (`StepRelLM2_4.ub`).
3. If `a` is initialized and `SubsliceInBounds count fromIdx toIdx fromEnd`
   holds, both machines step to `StateRelLM2_4`-related states
   (`StepRelLM2_4.step`): `_d` holds
   `.init (.aggregate 0 ((elems.drop fromIdx).take cnt))` backed by a fresh
   stack allocation (`MemPlaceRel`), and `a` stays initialized even when
   `isMove = true`. -/
theorem step_subslice_assign_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {d arrIdx : Local} {isMove : Bool}
    {fromIdx toIdx : Nat} {fromEnd : Bool} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨d, .nil⟩ (.use (subsliceReadOperand isMove arrIdx fromIdx toIdx fromEnd)),
            span⟩)
    {dDecl arrDecl : LocalDecl} {elemKind : RigidTy} {count : Nat}
    (hdecl_d : get? body.localDecls d = some dDecl)
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf_arr : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hwf_d : WellTypedArrayTy body.layouts dDecl.ty elemKind
      (subsliceEnd count toIdx fromEnd - fromIdx))
    (hd_uninit : get? s.frame.locals d = some .uninit)
    (hd_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame d) :
    let cnt := subsliceEnd count toIdx fromEnd - fromIdx
    ((get? s.frame.locals arrIdx = some .dead ∨
        (get? s.frame.locals arrIdx = some .uninit ∧
          (0 < count ∨ ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf arrIdx))) →
      stepMirFn body s = .fail .ub ∧
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)) →
      (fromEnd = true → count < fromIdx + toIdx → fromIdx + toIdx < 2 ^ 64 →
        stepMirFn body s = .fail .ub ∧
        StepRelLM2_4 body m (stepMirFn body s)
          (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
      (SubsliceInBounds count fromIdx toIdx fromEnd →
        ∃ (s' : MachineState) (m' : AnnealStepState)
          (mp_d : Miri.Interpreter.MemPlace AnnealProv)
          (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
          stepMirFn body s = .step s' ∧
          Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
            (m', .ok true) ∧
          StateRelLM2_4 body s' m' ∧
          get? s'.frame.locals d = some (.init (.aggregate 0 ((elems.drop fromIdx).take cnt))) ∧
          get? s'.frame.locals arrIdx = some (.init (.aggregate 0 elems)) ∧
          (∀ j, j ≠ d → get? s'.frame.locals j = get? s.frame.locals j) ∧
          m'.stack.frames = #[tf'] ∧
          (∃ c, tf'.locals[d]? = some ⟨.live (.indirect mp_d), c⟩) ∧
          MemPlaceRel m'.machine dDecl.ty body.layouts
            (some (.aggregate 0 ((elems.drop fromIdx).take cnt))) mp_d ∧
          LiveAllocsNodup m'.machine ∧
          (∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ d →
            IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
          s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
          StepPreservesHighWater m 1 (m', .ok true))) := by
  dsimp only
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  let op := subsliceReadOperand isMove arrIdx fromIdx toIdx fromEnd
  let cnt := subsliceEnd count toIdx fromEnd - fromIdx
  let layD := translateTy dDecl.ty body.layouts
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  have hstep_a : stepMirFn body s =
      evalStmt s ⟨.assign ⟨d, .nil⟩ (.use op), span⟩ body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt, op]
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hframe.lookup_local hdecl_d
  rw [hd_uninit] at hslot_d
  injection hslot_d with hslot_d
  subst hslot_d
  have hd_imm' := hd_imm topFrame hframes mls_d hmls_d
  have hloc_d' : LocalRel m.machine dDecl body.layouts .uninit mls_d := by
    cases hloc_d with
    | base _ _ hl => exact hl
  have hcache_d := hloc_d'.layout_eq
  have hmls_d_val : mls_d.value = .live (.immediate .uninit) := by
    cases hloc_d' with
    | indirect _ mp' _ _ _ _ => exact absurd rfl (hd_imm' mp')
    | immediate _ imm _ _ hv =>
      rcases hv with ⟨_, rfl⟩ | ⟨_, h, _⟩
      · rfl
      · cases h
  let topFrame₀ := cacheFrameLocalLayout topFrame d hlt_d layD
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 d none topFrame.localsIdentity, layD⟩
  have hevalPlace : annealEvalPlace body.localDecls body.layouts ⟨d, #[]⟩ m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_d hdecl_d (by rw [hmls_d_eq]; exact hcache_d)
  have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
      ⟨d, #[]⟩ true m = .ok destPlace m₀ := hevalPlace
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨d, #[]⟩
      (translateRvalue (.use op)) = true := by
    dsimp only [op]
    cases isMove <;>
      simp [lm24Assign, lm24Rvalue, lm24Operand, lm24Place, subsliceReadOperand,
        translateRvalue, translateOperand, translatePlace, translateProjectionElem,
        isSubsliceElem]
  have hm_pre : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨d, .nil⟩ (.use op), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) (some layD) >>=
          fun src => (annealRvalueHooksLM2_4 body.localDecls body.layouts).copyOp () src destPlace)
        m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace']
    dsimp only [translateRvalue]
    rfl
  have hframe₀ : FrameRelLM2_4 body m.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_d hlt_d
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ := hdisj.cache_layout hlt_d _
  have hstate₀ : StateRelLM2_4 body s m₀ :=
    StateRelLM2_4.mk topFrame₀ rfl hretCont ⟨retLay, hretPlace⟩ hframe₀ hcal hstack hbor hprot
      hcaller hdisj₀
  have hsim := evalSubsliceOperand_simulation hstate₀ rfl hnodup hdecl_arr hwf_arr isMove
    fromIdx toIdx fromEnd (some layD)
  dsimp only at hsim
  obtain ⟨hub_op, hinit_op⟩ := hsim
  refine ⟨?_, ?_⟩
  · intro hbad
    have hbad₀ : get? s.frame.locals arrIdx = some .dead ∨
        (get? s.frame.locals arrIdx = some .uninit ∧
          (0 < count ∨ IsImmediateFrameLocal topFrame₀ arrIdx)) := by
      rcases hbad with hdead | ⟨huninit, hpos | himm_arr⟩
      · exact Or.inl hdead
      · exact Or.inr ⟨huninit, Or.inl hpos⟩
      · exact Or.inr ⟨huninit, Or.inr ((himm_arr topFrame hframes).cache_layout hlt_d layD)⟩
    obtain ⟨ha_op_ub, m_err, msg, hm_op_err⟩ := hub_op hbad₀
    have ha_ub : evalStmt s ⟨.assign ⟨d, .nil⟩ (.use op), span⟩ body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue
      dsimp only
      rw [hbor, hcaller]
      simp [op, ha_op_ub]
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨d, .nil⟩ (.use op), span⟩) m =
        (m_err, .error (.undefinedBehavior msg)) := by
      rw [hm_pre]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error hm_op_err]
    rw [hstep_a, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_stmt]
    exact ⟨rfl, .ub _ _⟩
  · intro elems hinit_arr
    obtain ⟨mp_arr, topFrame₁, _, _, _, hother₁, htf₁_eq, hstate₁, hin_op, hoob_op⟩ :=
      hinit_op elems hinit_arr
    refine ⟨?_, ?_⟩
    · intro hfe hoob hlt64
      obtain ⟨ha_op_ub, msg, hm_op_err⟩ := hoob_op hfe hoob hlt64
      have ha_ub : evalStmt s ⟨.assign ⟨d, .nil⟩ (.use op), span⟩ body.localDecls body.layouts =
          MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue
        dsimp only
        rw [hbor, hcaller]
        simp [op, ha_op_ub]
      have hm_stmt : Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_4 body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨d, .nil⟩ (.use op), span⟩) m =
          ({ m₀ with stack := ⟨#[topFrame₁]⟩ }, .error (.undefinedBehavior msg)) := by
        rw [hm_pre]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error hm_op_err]
      rw [hstep_a, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
        hbb hstmt hm_stmt]
      exact ⟨rfl, .ub _ _⟩
    · intro hin
      obtain ⟨mem', id, hres⟩ := hcanRes
      obtain ⟨ha_op_ok, hm_op_ok, allocId, tag, baseAddr, relOffset, localAlloc,
        hprov_arr, hlive_arr, hbase_arr, hptr_arr, hslice_sub⟩ := hin_op hin
      have hd_ne_arr : d ≠ arrIdx := by
        intro heq; subst heq; rw [hd_uninit] at hinit_arr; cases hinit_arr
      rcases hstate₁ with ⟨tf₁_s, htf₁_s, _, _, hframe₁, _, _, _, _, _, hdisj₁⟩
      have htf₁_s_eq : tf₁_s = topFrame₁ := by simpa using htf₁_s.symm
      subst tf₁_s
      clear htf₁_s
      have hlt_d₁ : d < topFrame₁.locals.size := by
        rw [hframe₁.mf_locals_size, ← hframe.mf_locals_size]
        exact hlt_d
      have hmls_d₁ : topFrame₁.locals[d]? = some { mls_d with layout := some layD } := by
        rw [hother₁ d hd_ne_arr]
        dsimp only [topFrame₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set_self, hmls_d_eq]
      have hd₁ : topFrame₁.locals[d]'hlt_d₁ = { mls_d with layout := some layD } := by
        have h := Array.getElem?_eq_getElem hlt_d₁
        rw [hmls_d₁] at h
        exact (Option.some.inj h).symm
      have hc_d₁ : (topFrame₁.locals[d]'hlt_d₁).layout = some layD := by rw [hd₁]
      have hval_d₁ : (topFrame₁.locals[d]'hlt_d₁).value = .live (.immediate .uninit) := by
        rw [hd₁]; exact hmls_d_val
      let arrLay := translateTy arrDecl.ty body.layouts
      let es := (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size
      let subMp : Miri.Interpreter.MemPlace AnnealProv :=
        { mp_arr with
          ptr := { mp_arr.ptr with
            offset := Miri.ABI.Size.ofBytes
              (mp_arr.ptr.offset.bytes + es.bytes * UInt64.ofNat fromIdx) },
          metadata := .none }
      let srcLay : Miri.Interpreter.LocalLayout :=
        { ty := arrLay.ty,
          layout := { arrLay.layout with
            fields := .Array es (UInt64.ofNat cnt),
            size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt) } }
      have hfrom_le : fromIdx ≤ count := by
        rcases hin with ⟨_, h1, h2⟩ | ⟨_, h1⟩ <;> omega
      have hcnt32 := hwf_arr.count_lt_two_pow_32
      have htot_arr := hwf_arr.total_bytes_bound
      have hfrom_toNat : (UInt64.ofNat fromIdx).toNat = fromIdx := by
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt
          (by simpa [UInt64.size] using (by omega : fromIdx < 2 ^ 64))]
      have hprod_lt : fromIdx * es.bytes.toNat < 2 ^ 64 := by
        have hle := Nat.mul_le_mul_right es.bytes.toNat hfrom_le
        dsimp only [es] at hle htot_arr ⊢
        omega
      have hmul_eq : es.bytes * UInt64.ofNat fromIdx =
          UInt64.ofNat (fromIdx * es.bytes.toNat) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_mul, hfrom_toNat, Nat.mul_comm,
          Nat.mod_eq_of_lt (by simpa [UInt64.size] using hprod_lt),
          UInt64.toNat_ofNat',
          Nat.mod_eq_of_lt (by simpa [UInt64.size] using hprod_lt)]
      have hsrcOff : Miri.ABI.Size.ofBytes (subMp.ptr.offset.bytes - baseAddr) =
          Miri.ABI.Size.ofBytes
            (relOffset.bytes + UInt64.ofNat (fromIdx * es.bytes.toNat)) := by
        have hsub_bytes : subMp.ptr.offset.bytes =
            baseAddr + (relOffset.bytes + es.bytes * UInt64.ofNat fromIdx) := by
          dsimp only [subMp]
          rw [hptr_arr]
          simp [Miri.ABI.Size.ofBytes, UInt64.add_assoc]
        rw [hsub_bytes, uint64_add_sub_cancel_left, hmul_eq]
      let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
      obtain ⟨dest', hmemcopy, hdest_sz, hslice_d⟩ :=
        annealMemCopyOp_freshArray (body := body) (m := m₁) rfl hlt_d₁ hdecl_d hwf_d hc_d₁
          hval_d₁ hres hnodup (subMp := subMp) hprov_arr hlive_arr hbase_arr hsrcOff hslice_sub
          srcLay topFrame.localsIdentity
      have huse : usesMemCopy ⟨.indirect subMp, srcLay⟩ = true := rfl
      have hm_op_ok' : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
          (some layD) m₀ = .ok ⟨.indirect subMp, srcLay⟩ m₁ := hm_op_ok
      let mp_d := stackAllocPlace id
      let mach₃ := stackAllocMachine m.machine mem' id dest'
      let tf₃ := setFrameLocalIndirect topFrame₁ d hlt_d₁ mp_d
      let st₃ : AnnealStepState := { stack := ⟨#[tf₃]⟩, machine := mach₃ }
      have hm_stmt : Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_4 body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨d, .nil⟩ (.use op), span⟩) m = (st₃, .ok ()) := by
        rw [hm_pre]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hm_op_ok']
        simp only [annealRvalueHooksLM2_4, huse, ↓reduceIte]
        rw [hmemcopy]
      have htf₁_loc : topFrame₁.location = topFrame₀.location := by rw [htf₁_eq]
      have hloc₃ : tf₃.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
        show topFrame₁.location = _
        rw [htf₁_loc]
        exact hframe.location_eq
      have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
        hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl hloc₃
      -- Anneal: `_d` receives `.init (.aggregate 0 sub)` and `arrIdx` stays
      -- initialized.
      let sub := (elems.drop fromIdx).take cnt
      have hvld_sub : validateLoadedValue body.layouts body.localDecls op (.aggregate 0 sub) =
          true := by
        have hpt : placeTy body.localDecls body.layouts
            ⟨arrIdx, [.subslice fromIdx toIdx fromEnd]⟩ = some arrDecl.ty := by
          simp [placeTy, hdecl_arr, resolveProjectedTy]
        cases isMove <;>
          simp [op, subsliceReadOperand, validateLoadedValue, operandTy, hpt, hwf_arr.arr_kind]
      have hrv : evalRvalue s.frame.locals (.use op) s.memory body.localDecls body.layouts =
          .ok (.aggregate 0 sub) s.frame.locals s.memory := by
        unfold evalRvalue
        dsimp only
        rw [hbor, hcaller, ha_op_ok]
        dsimp only
        change (match validateLoadedValue body.layouts body.localDecls op (.aggregate 0 sub) with
          | false => _ | true => _) = _
        rw [hvld_sub]
        cases isMove <;> rfl
      let locals₂ := s.frame.locals.set d (.init (.aggregate 0 sub))
      have ha_ok : evalStmt s ⟨.assign ⟨d, .nil⟩ (.use op), span⟩ body.localDecls body.layouts =
          MirStepNode.step (advanceStmt s locals₂ s.memory) := by
        unfold evalStmt
        dsimp only
        rw [hrv]
        simp only []
        rw [hprot, hbor]
        dsimp only [invalidateConflictingBorrows]
        rw [hmem_same]
        simp [hd_uninit, set?_eq_some_set hlt_af_d, locals₂]
      -- Post-state `MemPlaceRel` and `StateRelLM2_4`.
      obtain ⟨hlive_b, hfreshne, hbase_b⟩ :=
        stackAllocMachine_live_base (mach := m.machine) dest' hres
      have hmp_d : MemPlaceRel mach₃ dDecl.ty body.layouts (some (.aggregate 0 sub)) mp_d := by
        refine stackAlloc_memPlaceRel hslice_d.alloc_mut
          (translateTy_align_pow2_le_29 dDecl.ty body.layouts)
          hdest_sz
          (fun h => nomatch h)
          (fun _ _ _ => ?_)
          (fun _ h => nomatch h)
          (fun ek cnt' es' hk hopt => ?_)
        · rw [hslice_d.alloc_mask, hdest_sz]
          have hend_d : (Miri.Memory.allocRange Miri.ABI.Size.ZERO
              (translateTy dDecl.ty body.layouts).layout.size).endExclusive =
              .ok (translateTy dDecl.ty body.layouts).layout.size := by
            have hlt0 : Miri.ABI.Size.ZERO.bytes.toNat +
                (translateTy dDecl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64 := by
              simp [Miri.ABI.Size.ZERO]; exact UInt64.toNat_lt _
            have h := allocRange_endExclusive_of_lt (off := Miri.ABI.Size.ZERO)
              (sz := (translateTy dDecl.ty body.layouts).layout.size) hlt0
            simpa [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes] using h
          exact Miri.Memory.InitMask.lazy_initialized_query _ _ _ hend_d (UInt64.le_refl _)
        · rw [hwf_d.arr_kind] at hk
          injection hk with hek hcnt'
          subst hek hcnt'
          injection hopt with hagg
          injection hagg with _ hes'
          subst hes'
          exact ⟨hwf_d.arr_fields, hwf_d.arr_size, hwf_d.arr_align, hslice_d⟩
      let tf_fin := { tf₃ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
      let m' : AnnealStepState := { st₃ with stack := ⟨#[tf_fin]⟩ }
      have htf₁_rc : topFrame₁.returnContinuation = topFrame₀.returnContinuation := by rw [htf₁_eq]
      have htf₁_rp : topFrame₁.returnPlace = topFrame₀.returnPlace := by rw [htf₁_eq]
      have htf₁_id : topFrame₁.localsIdentity = topFrame₀.localsIdentity := by rw [htf₁_eq]
      have hframe_fin : FrameRelLM2_4 body mach₃ (advanceStmt s locals₂ s.memory).frame tf_fin :=
        { body_eq := hframe₁.body_eq
          location_eq := rfl
          af_locals_len := by
            show (s.frame.locals.set d _).length = _
            rw [List.length_set]
            exact hframe.af_locals_len
          mf_locals_size := by
            show (topFrame₁.locals.set d _ hlt_d₁).size = _
            rw [Array.size_set]
            exact hframe₁.mf_locals_size
          locals_rel := by
            intro i decl slot mls hdecl hslot hmls
            have hslot' : get? locals₂ i = some slot := hslot
            have hmls' : (topFrame₁.locals.set d
                { topFrame₁.locals[d]'hlt_d₁ with value := .live (.indirect mp_d) } hlt_d₁)[i]? =
                some mls := hmls
            rw [get?_eq_getElem?, List.getElem?_set] at hslot'
            rw [Array.getElem?_set] at hmls'
            by_cases hid : d = i
            · subst hid
              simp only [↓reduceIte, hlt_af_d, Option.some.injEq] at hslot' hmls'
              subst hslot' hmls'
              rw [hdecl_d] at hdecl
              cases hdecl
              refine .base _ _ (.indirect (.init (.aggregate 0 sub)) mp_d _ ?_ nofun hmp_d)
              intro l hl
              rw [hc_d₁] at hl
              exact (Option.some.inj hl).symm
            · simp only [hid, ↓reduceIte] at hslot' hmls'
              exact (hframe₁.locals_rel i decl slot mls hdecl hslot' hmls').of_live_base hlive_b
                hbase_b }
      have hdisj_fin : MemoryAllocDisjoint tf_fin := by
        intro i j mp_i mp_j lay_i lay_j hij hi hj
        dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hi hj
        rw [Array.getElem?_set] at hi hj
        by_cases hi_d : d = i
        · subst hi_d
          have hj_d : d ≠ j := hij
          simp only [hj_d, ↓reduceIte] at hj
          simp only [↓reduceIte] at hi
          obtain ⟨a, la', ha, hla⟩ := hframe₁.indirect_allocId hj
          injection hi with hi
          injection hi with hv _
          injection hv with hv
          injection hv with hv
          subst hv
          rw [ha]
          simp only [mp_d, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
            Option.some.injEq]
          exact fun h => hfreshne a la' hla h.symm
        · simp only [hi_d, ↓reduceIte] at hi
          by_cases hj_d : d = j
          · subst hj_d
            simp only [↓reduceIte] at hj
            obtain ⟨a, la', ha, hla⟩ := hframe₁.indirect_allocId hi
            injection hj with hj
            injection hj with hv _
            injection hv with hv
            injection hv with hv
            subst hv
            rw [ha]
            simp only [mp_d, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
              Option.some.injEq]
            exact hfreshne a la' hla
          · simp only [hj_d, ↓reduceIte] at hj
            exact hdisj₁ i j mp_i mp_j lay_i lay_j hij hi hj
      have hstate' : StateRelLM2_4 body (advanceStmt s locals₂ s.memory) m' :=
        StateRelLM2_4.mk tf_fin rfl (by show topFrame₁.returnContinuation = _; rw [htf₁_rc]; exact hretCont)
          ⟨retLay, by
            show topFrame₁.returnPlace = .frameLocal 0 0 none retLay topFrame₁.localsIdentity
            rw [htf₁_rp, htf₁_id]
            exact hretPlace⟩
          hframe_fin hcal hstack hbor hprot hcaller hdisj_fin
      have himm_fin : ∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ d →
          IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf_fin j := by
        intro tf htf j hj himm_j
        rw [hframes] at htf
        have htf' : topFrame = tf := by simpa using htf
        subst htf'
        have h₀ := himm_j.cache_layout hlt_d layD
        intro mls hmls
        dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hmls
        rw [Array.getElem?_set_ne _ (Ne.symm hj)] at hmls
        by_cases hj_arr : j = arrIdx
        · subst hj_arr
          obtain ⟨_, mls_a₀, _, _, hslot_a, hmls_a₀, _, hloc_a⟩ := hframe₀.lookup_local hdecl_arr
          rw [hinit_arr] at hslot_a; injection hslot_a with hslot_a; subst hslot_a
          cases hloc_a with
          | union _ _ _ _ _ _ _ _ hwt _ _ _ =>
            obtain ⟨n, hn, _⟩ := hwt.fields_union; rw [hwf_arr.arr_fields] at hn; cases hn
          | base _ _ hl =>
            obtain ⟨mp_a, c_a, hm_eq, _, _⟩ := hl.array_init_is_indirect hwf_arr.arr_kind
            rw [hm_eq] at hmls_a₀
            exact absurd rfl (h₀ _ hmls_a₀ mp_a)
        · rw [hother₁ j hj_arr] at hmls
          exact h₀ mls hmls
      refine ⟨advanceStmt s locals₂ s.memory, m', mp_d, tf_fin, by rw [hstep_a, ha_ok],
        hstep_m, hstate', ?_, ?_, ?_, rfl, ⟨(topFrame₁.locals[d]'hlt_d₁).layout, ?_⟩,
        hmp_d, LiveAllocsNodup.stackAllocMachine dest' hnodup hres, himm_fin, rfl, rfl,
        fun _ hw hb => MemoryHighWater.stackAllocMachine dest' hw hb hres⟩
      · simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_d, sub, cnt]
      · simp only [advanceStmt, locals₂, get?_eq_getElem?, List.getElem?_set_ne hd_ne_arr]
        rwa [← get?_eq_getElem?]
      · intro j hj
        simp [advanceStmt, locals₂, get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hj)]
      · simp [tf_fin, tf₃, setFrameLocalIndirect]

/-! ## 16. Overwrites, Dead Destinations, Self-Copy Overlap & Uninitialized Union Copy (`A2`)

Sections 6–7 and 15 proved union aggregate initialization, whole-union
`copy`/`move`, and `Subslice` assignment into fresh immediate `.uninit`
destinations. Once a union or array local has been written once, `lean-miri`
keeps it memory-backed (`.live (.indirect mp)`) across subsequent assignments,
so later assignments take the in-place overwrite path through
`annealForceUnionAllocation` and `Allocation.copy` / `Allocation.writeScalar`, while
dead destination locals take `annealForceUnionAllocation`'s `.undefinedBehavior`
branch. This section proves lockstep correspondence and exact semantic boundary
theorems across those overwrite and edge paths. -/

theorem UnionLocalRel.dead_value
    {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : UnionLocalRel mach decl layouts .dead mls) :
    mls.value = .dead := by
  cases h with
  | base _ _ hl =>
    cases hl with
    | dead _ _ => rfl
    | immediate _ _ _ _ hv => rcases hv with ⟨hs, _⟩ | ⟨_, hs, _⟩ <;> cases hs
    | indirect _ _ _ _ hne _ => exact absurd rfl hne

/-- `annealForceUnionAllocation` on a `.dead` destination local reports
`StepError.undefinedBehavior "write to dead local"`. -/
theorem annealForceUnionAllocation_dead_err
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Nat} (hlt : idx < tf.locals.size)
    (hdead : (tf.locals[idx]'hlt).value = .dead)
    (ident : Miri.Interpreter.LocalsIdentity) (lay : Miri.Interpreter.LocalLayout) :
    annealForceUnionAllocation body.localDecls body.layouts ⟨.local 0 idx none ident, lay⟩ m =
      .error (.undefinedBehavior "write to dead local") m := by
  have hgo : tf.getLocalOperand idx = .error (.localExpectedLive idx) := by
    unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
      Miri.Interpreter.LocalState.access
    simp [hlt, hdead, bind, Except.bind, pure, Except.pure, Except.mapError]
  have hraw : Miri.Interpreter.forceAllocation (annealPlaceHooks body.localDecls body.layouts) ()
      ⟨.local 0 idx none ident, lay⟩ m =
      .error (.stack (.localExpectedLive idx)) m := by
    with_unfolding_all
      unfold Miri.Interpreter.forceAllocation
      simp only [Miri.Interpreter.requireCurrent_eq,
        Miri.Interpreter.checkLocalIdentity_debugOff (annealPlaceHooks _ _) _ rfl,
        bind, Bind.bind, EStateM.bind, annealPlaceHooks_frameIndex_eq hframes, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, pure, Pure.pure, EStateM.pure,
        annealPlaceHooks_getFrame_eq hframes, hgo]
      rfl
  unfold annealForceUnionAllocation
  rw [hraw]

/-- `annealForceUnionAllocation` on an already memory-backed destination local returns
its existing `MemPlace` without allocating or changing state. -/
theorem annealForceUnionAllocation_indirect_eq
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Nat} (hlt : idx < tf.locals.size)
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hind : (tf.locals[idx]'hlt).value = .live (.indirect mp))
    (ident : Miri.Interpreter.LocalsIdentity) (lay : Miri.Interpreter.LocalLayout) :
    annealForceUnionAllocation body.localDecls body.layouts ⟨.local 0 idx none ident, lay⟩ m =
      .ok ⟨mp, lay⟩ m := by
  have hgo : tf.getLocalOperand idx = .ok (.indirect mp) := by
    unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
      Miri.Interpreter.LocalState.access
    simp [hlt, hind, bind, Except.bind, pure, Except.pure, Except.mapError]
  apply annealForceUnionAllocation_of_ok
  unfold Miri.Interpreter.forceAllocation
  simp only [Miri.Interpreter.requireCurrent_eq,
    Miri.Interpreter.checkLocalIdentity_debugOff (annealPlaceHooks _ _) _ rfl,
    bind, EStateM.bind, annealPlaceHooks_frameIndex_eq hframes, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure, annealPlaceHooks_getFrame_eq hframes,
    hgo, Miri.Interpreter.stackLift_ok]

/-- `annealMemCopyOp` from a memory-backed union `mp_u` (`allocId`) into an
already memory-backed destination local `w` (`mp_w` at `destId`, at offset `0`)
runs `Miri.Memory.Allocation.copy` with `sameAllocation = (allocId == destId)`
and updates `destId`'s entry in `m.machine.memory.live` in place. -/
theorem annealMemCopyOp_inplaceUnion
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {w : Nat} {wDecl : LocalDecl} (hlt : w < tf.locals.size)
    {mp_w : Miri.Interpreter.MemPlace AnnealProv}
    (hval : (tf.locals[w]'hlt).value = .live (.indirect mp_w))
    (hnodup : LiveAllocsNodup m.machine)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    {allocId destId : Miri.Memory.AllocId}
    {tag_u tag_w : Miri.Memory.BorTag} {base_u base_w : UInt64}
    {la_u la_w : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hprov_u : mp_u.ptr.provenance = some (.concrete allocId tag_u))
    (hlive_u : (allocId, la_u) ∈ m.machine.memory.live.toList)
    (hbase_u : m.machine.lookupBaseAddr allocId = some base_u)
    (hptr_u : mp_u.ptr.offset = Miri.ABI.Size.ofBytes base_u)
    (hprov_w : mp_w.ptr.provenance = some (.concrete destId tag_w))
    (hlive_w : (destId, la_w) ∈ m.machine.memory.live.toList)
    (hbase_w : m.machine.lookupBaseAddr destId = some base_w)
    (hptr_w : mp_w.ptr.offset = Miri.ABI.Size.ofBytes base_w)
    (hsz_nz : ((translateTy wDecl.ty body.layouts).layout.size.bytes == 0) = false)
    (srcLay : Miri.Interpreter.LocalLayout) (ident : Miri.Interpreter.LocalsIdentity) :
    ∃ (destIdx : Nat),
      m.machine.memory.live.findIdx? (fun (k, _) => k == destId) = some destIdx ∧
      m.machine.memory.live[destIdx]? = some (destId, la_w) ∧
      (∀ A' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
        Miri.Memory.Allocation.copy la_u.allocation
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy wDecl.ty body.layouts).layout.size)
            Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) (allocId == destId) true la_w.allocation =
          .ok () A' →
        annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp_u, srcLay⟩
            ⟨.local 0 w none ident, translateTy wDecl.ty body.layouts⟩ m =
          .ok () { m with machine := inplaceMachine m.machine destIdx destId la_w.kind A' } ∧
        LiveAllocsNodup (inplaceMachine m.machine destIdx destId la_w.kind A') ∧
        (destId, ⟨la_w.kind, A'⟩) ∈
          (inplaceMachine m.machine destIdx destId la_w.kind A').memory.live.toList ∧
        (∀ a la, a ≠ destId → (a, la) ∈ m.machine.memory.live.toList →
          (a, la) ∈ (inplaceMachine m.machine destIdx destId la_w.kind A').memory.live.toList)) ∧
      (∀ err A_err,
        Miri.Memory.Allocation.copy la_u.allocation
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy wDecl.ty body.layouts).layout.size)
            Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) (allocId == destId) true la_w.allocation =
          .error err A_err →
        annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp_u, srcLay⟩
            ⟨.local 0 w none ident, translateTy wDecl.ty body.layouts⟩ m =
          .error (annealMemCopyError err) m) := by
  have hforce := annealForceUnionAllocation_indirect_eq (body := body) hframes hlt hval ident
    (translateTy wDecl.ty body.layouts)
  have hfind_u := array_find?_of_nodup_fst hnodup hlive_u
  obtain ⟨destIdx, _, hfindIdx_w, hget_w, hset_w⟩ := array_findIdx?_of_nodup_fst hnodup hlive_w
  have hsrcOff : Miri.ABI.Size.ofBytes (mp_u.ptr.offset.bytes - base_u) = Miri.ABI.Size.ZERO := by
    rw [hptr_u]; simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
  have hdestOff : Miri.ABI.Size.ofBytes (mp_w.ptr.offset.bytes - base_w) = Miri.ABI.Size.ZERO := by
    rw [hptr_w]; simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
  rcases la_w with ⟨kind_w, alloc_w⟩
  refine ⟨destIdx, hfindIdx_w, hget_w, fun A' hcopy => ?_, fun err A_err herr => ?_⟩
  · obtain ⟨hnodup', hmem', hother⟩ := hset_w ⟨kind_w, A'⟩
    refine ⟨?_, hnodup', hmem', hother⟩
    unfold annealMemCopyOp
    simp only [bind, EStateM.bind, hforce, get, getThe, MonadStateOf.get, EStateM.get,
      hprov_u, hprov_w, Option.bind, Miri.Memory.Provenance.getAllocId, hbase_u, hbase_w,
      hfind_u, hfindIdx_w, hget_w, hsrcOff, hdestOff, hsz_nz, Bool.false_eq_true, ↓reduceIte,
      hcopy, set, MonadStateOf.set, EStateM.set]
    rfl
  · unfold annealMemCopyOp
    simp only [bind, EStateM.bind, hforce, get, getThe, MonadStateOf.get, EStateM.get,
      hprov_u, hprov_w, Option.bind, Miri.Memory.Provenance.getAllocId, hbase_u, hbase_w,
      hfind_u, hfindIdx_w, hget_w, hsrcOff, hdestOff, hsz_nz, Bool.false_eq_true, ↓reduceIte,
      herr, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- Whole-union `copy` (`isMove = false`) or `move` (`isMove = true`) operand. -/
def unionWholeOperand (isMove : Bool) (u : Local) : MirAst.Operand :=
  if isMove then .move ⟨u, .nil⟩ else .copy ⟨u, .nil⟩

/-- **`step_union_whole_copy_or_move_overwrite_simulation`** (`LM-2.4` `A2`):
statement-level simulation for `_w = copy _u` or `_w = move _u` across dead /
uninitialized sources, dead destinations, in-place overwrites of an already
memory-backed `UnionMemRel` destination `_w` (including narrowing the
initialized prefix from `sc_old.sizeBytes` down to `sc.sizeBytes`, clearing
`[sc.sizeBytes, sc_old.sizeBytes)` in the `InitMask` via `union_copy_alloc_spec`),
and self-move `_u = move _u`. -/
theorem step_union_whole_copy_or_move_overwrite_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {w u : Local} {isMove : Bool} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩)
    {wDecl uDecl : LocalDecl} (hdecl_w : get? body.localDecls w = some wDecl)
    (hdecl_u : get? body.localDecls u = some uDecl) (hty : wDecl.ty = uDecl.ty)
    {S n : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields_u : (translateTy uDecl.ty body.layouts).layout.fields = .Union n := by rfl) :
    -- (1) Dead source `_u`, or immediate uninitialized `_u`: UB in both.
    ((get? s.frame.locals u = some .dead ∨
        (get? s.frame.locals u = some .uninit ∧
          ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf u)) →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    -- (2) Dead destination `_w` with initialized `UnionMemRel` source `_u`: UB in both.
    (∀ f f0Ty sc mp_u,
      f < n →
      get? s.frame.locals u =
        some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) →
      (∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[u]? = some ⟨.live (.indirect mp_u), c⟩) →
      UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp_u →
      get? s.frame.locals w = some .dead →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    -- (3) In-place overwrite (`w ≠ u`) of an already memory-backed `UnionMemRel` `_w`
    --     (arbitrary old `f_old, f0Ty_old, sc_old`, even `sc_old.sizeBytes > sc.sizeBytes`):
    --     both step to `StateRelLM2_4` with `0` fresh allocations.
    (∀ f f_old f0Ty sc mp_u f0Ty_old sc_old mp_w,
      w ≠ u → f < n → f_old < n →
      get? s.frame.locals u =
        some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) →
      (∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[u]? = some ⟨.live (.indirect mp_u), c⟩) →
      UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp_u →
      get? s.frame.locals w =
        some (.init (.aggregate 0 (unionSlotFields n f_old (.scalar sc_old)))) →
      (∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[w]? = some ⟨.live (.indirect mp_w), c⟩) →
      UnionMemRel m.machine wDecl.ty body.layouts S f0Ty_old sc_old mp_w →
      ∃ (s' : MachineState) (m' : AnnealStepState)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        stepMirFn body s = .step s' ∧
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals w =
          some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) ∧
        get? s'.frame.locals u =
          (if isMove then some .uninit
           else some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))) ∧
        m'.stack.frames = #[tf'] ∧
        (∃ c, tf'.locals[w]? = some ⟨.live (.indirect mp_w), c⟩) ∧
        UnionMemRel m'.machine wDecl.ty body.layouts S f0Ty sc mp_w ∧
        LiveAllocsNodup m'.machine ∧
        StepPreservesHighWater m 0 (m', .ok true)) := by
  rcases hstate with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot; generalize s.memory = mem; intro hbor hprot; cases mem
    dsimp only at hbor hprot; subst hbor hprot; rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩
      body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
  have hwt_w : WellTypedUnionTy body.layouts wDecl.ty S := hty ▸ hwt
  have hS := hwt.size_valid
  have hS16 : S ≤ 16 := by rcases hS with h | h | h | h | h <;> omega
  have hunion_w := isUnionLocal_of_wellTyped hdecl_w hwt_w
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨w, #[]⟩
      (translateRvalue (.use (unionWholeOperand isMove u))) = true := by
    simp [lm24Assign, lm24Place, hunion_w]
  obtain ⟨slot_w0, mls_w0, hlt_af_w, hlt_w, hslot_w0, hmls_w0, hmls_w_eq, hloc_w0⟩ :=
    hframe.lookup_local hdecl_w
  let layW := translateTy wDecl.ty body.layouts
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame w hlt_w layW
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 w none topFrame.localsIdentity, layW⟩
  have hevalPlace : annealEvalPlace body.localDecls body.layouts ⟨w, #[]⟩ m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_w hdecl_w (by rw [hmls_w_eq]; exact hloc_w0.layout_eq)
  have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
      ⟨w, #[]⟩ true m = .ok destPlace m₀ := hevalPlace
  have hframe₀ : FrameRelLM2_4 body m.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_w hlt_w
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ := hdisj.cache_layout hlt_w _
  refine ⟨?_, ?_, ?_⟩
  · -- (1) Dead or immediate-uninit `_u`.
    intro hsrc
    obtain ⟨slot_u0, mls_u0, _, hlt_u0, hslot_u0, hmls_u0, hmls_u0_eq, hloc_u0⟩ :=
      hframe₀.lookup_local hdecl_u
    rcases hsrc with hu_dead | ⟨hu_uninit, hu_imm⟩
    · rw [hu_dead] at hslot_u0; injection hslot_u0 with hslot_u0; subst hslot_u0
      have hdead_val := hloc_u0.dead_value
      have hm0_dead : topFrame₀.locals[u]'hlt_u0 = ⟨.dead, mls_u0.layout⟩ := by
        rw [hmls_u0_eq]; cases mls_u0; cases hdead_val; rfl
      have hop_err : annealEvalOperandLM2_4 body.localDecls body.layouts
          (translateOperand (unionWholeOperand isMove u)) (some layW) m₀ =
          .error (.undefinedBehavior "read of dead local")
            { m₀ with stack := ⟨#[cacheFrameLocalLayout topFrame₀ u hlt_u0 layU]⟩ } := by
        cases isMove
        · exact annealEvalOperand_copy_dead (m := m₀) rfl hlt_u0 hdecl_u hm0_dead
            hloc_u0.layout_eq
        · exact annealEvalOperand_move_dead (m := m₀) rfl hlt_u0 hdecl_u hm0_dead
            hloc_u0.layout_eq
      have ha_ub : evalStmt s ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue; dsimp only; rw [hbor, hcaller]
        cases isMove <;> simp [unionWholeOperand, evalOperand, hu_dead]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_4 body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩) m =
          ({ m₀ with stack := ⟨#[cacheFrameLocalLayout topFrame₀ u hlt_u0 layU]⟩ },
           .error (.undefinedBehavior "read of dead local")) := by
        have hpre : Miri.Interpreter.Step.evalStatement
            (annealStepHooksLM2_4 body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩) m =
            Miri.Interpreter.runRvalue
              (annealEvalOperandLM2_4 body.localDecls body.layouts
                (translateOperand (unionWholeOperand isMove u)) (some layW) >>= fun op =>
                (annealRvalueHooksLM2_4 body.localDecls body.layouts).copyOp () op destPlace) m₀ := by
          unfold Miri.Interpreter.Step.evalStatement translateStmt
          dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
          simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
          apply runRvalue_eq_of_eq
          unfold Miri.Interpreter.evalRvalueIntoPlace
          rw [EStateM.bind_eq_ok hevalPlace']
          dsimp only [translateRvalue]
          rfl
        rw [hpre]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error hop_err]
      rw [hstep_a, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
        hbb hstmt hm_err]
      exact .ub _ _
    · rw [hu_uninit] at hslot_u0; injection hslot_u0 with hslot_u0; subst hslot_u0
      have hu_imm0' := ((hu_imm topFrame hframes).cache_layout hlt_w layW) mls_u0 hmls_u0
      have hc_u0 := hloc_u0.layout_eq
      have huninit_val : mls_u0.value = .live (.immediate .uninit) := by
        cases hloc_u0 with
        | base _ _ hl =>
          cases hl with
          | indirect _ mp' _ _ _ _ => exact absurd rfl (hu_imm0' mp')
          | immediate _ imm _ _ hv =>
            rcases hv with ⟨_, rfl⟩ | ⟨_, h, _⟩
            · rfl
            · cases h
      let tf_u := cacheFrameLocalLayout topFrame₀ u hlt_u0 layU
      have hlt_u' : u < tf_u.locals.size := by dsimp [tf_u]; rw [cacheFrameLocalLayout_size]; exact hlt_u0
      let tf_op := if isMove then deinitFrameLocal tf_u u hlt_u' else tf_u
      have hop_ok : annealEvalOperandLM2_4 body.localDecls body.layouts
          (translateOperand (unionWholeOperand isMove u)) (some layW) m₀ =
          .ok ⟨.immediate .uninit, layU⟩ { m with stack := ⟨#[tf_op]⟩ } := by
        have hm0_val : (topFrame₀.locals[u]'hlt_u0) = ⟨.live (.immediate .uninit), mls_u0.layout⟩ := by
          rw [hmls_u0_eq]; cases mls_u0; cases huninit_val; rfl
        cases isMove
        · exact annealEvalOperand_copy_live (m := m₀) rfl hlt_u0 hdecl_u hm0_val hc_u0
        · exact annealEvalOperand_move_live (m := m₀) rfl hlt_u0 hdecl_u hm0_val hc_u0
      have huse : usesMemCopy ⟨.immediate .uninit, layU⟩ = false := rfl
      have ha_ub : evalStmt s ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue; dsimp only; rw [hbor, hcaller]
        cases isMove <;> simp [unionWholeOperand, evalOperand, hu_uninit]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_4 body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩) m =
          ({ m with stack := ⟨#[tf_op]⟩ }, .error (.undefinedBehavior "read of uninitialized local")) := by
        have hpre : Miri.Interpreter.Step.evalStatement
            (annealStepHooksLM2_4 body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩) m =
            Miri.Interpreter.runRvalue
              (do
                let imm ← annealReadImmediateLM2_2 ⟨.immediate .uninit, layU⟩
                annealWriteImmediateLM2_2 imm.imm destPlace) { m with stack := ⟨#[tf_op]⟩ } := by
          unfold Miri.Interpreter.Step.evalStatement translateStmt
          dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
          simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
          apply runRvalue_eq_of_eq
          unfold Miri.Interpreter.evalRvalueIntoPlace
          rw [EStateM.bind_eq_ok hevalPlace']
          dsimp only [translateRvalue]
          have hop_ok' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
              (Miri.Interpreter.OperandPath.rvalue "operand")
              (translateOperand (unionWholeOperand isMove u))
              (some ((annealRvalueHooksLM2_4 body.localDecls body.layouts).placeLayout destPlace)) m₀ =
              .ok ⟨.immediate .uninit, layU⟩ { m with stack := ⟨#[tf_op]⟩ } := hop_ok
          rw [EStateM.bind_eq_ok hop_ok']
          simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2, huse, Bool.false_eq_true, ↓reduceIte]
        rw [hpre]
        rfl
      rw [hstep_a, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
        hbb hstmt hm_err]
      exact .ub _ _
  · -- (2) Dead destination `_w` with `UnionMemRel` source `_u`.
    intro f f0Ty sc mp_u hf hu_slot hu_mls hmem_u hw_dead
    have hwu : w ≠ u := by intro heq; subst heq; rw [hw_dead] at hu_slot; cases hu_slot
    rw [hw_dead] at hslot_w0; injection hslot_w0 with hslot_w0; subst hslot_w0
    have hw_dead_val := hloc_w0.dead_value
    obtain ⟨c_u, hmls_u⟩ := hu_mls topFrame hframes
    obtain ⟨_, mls_u, hlt_af_u, hlt_u, _, hmls_u', _, hloc_u⟩ := hframe.lookup_local hdecl_u
    rw [hmls_u] at hmls_u'; injection hmls_u' with hmls_u'; subst hmls_u'
    have hlt_u₀ : u < topFrame₀.locals.size := by dsimp [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
    have hmls_u₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp_u), c_u⟩ := by
      have h := Array.getElem?_eq_getElem hlt_u₀
      dsimp only [topFrame₀, cacheFrameLocalLayout] at h ⊢
      rw [Array.getElem?_set_ne _ hwu, hmls_u] at h
      exact (Option.some.inj h).symm
    let tf_u := cacheFrameLocalLayout topFrame₀ u hlt_u₀ layU
    have hlt_u' : u < tf_u.locals.size := by dsimp [tf_u]; rw [cacheFrameLocalLayout_size]; exact hlt_u₀
    let tf₁ := if isMove then deinitFrameLocal tf_u u hlt_u' else tf_u
    let m₁ : AnnealStepState := { m with stack := ⟨#[tf₁]⟩ }
    have hop_ok : annealEvalOperandLM2_4 body.localDecls body.layouts
        (translateOperand (unionWholeOperand isMove u)) (some layW) m₀ =
        .ok ⟨.indirect mp_u, layU⟩ m₁ := by
      cases isMove
      · exact annealEvalOperand_copy_live (m := m₀) rfl hlt_u₀ hdecl_u hmls_u₀ hloc_u.layout_eq
      · exact annealEvalOperand_move_live (m := m₀) rfl hlt_u₀ hdecl_u hmls_u₀ hloc_u.layout_eq
    have huse : usesMemCopy ⟨.indirect mp_u, layU⟩ = true := by simp [usesMemCopy, layU, hfields_u]
    have hlt_w₁ : w < tf₁.locals.size := by
      cases isMove <;> simp [tf₁, tf_u, topFrame₀, deinitFrameLocal, cacheFrameLocalLayout_size, hlt_w]
    have hval_w₁ : (tf₁.locals[w]'hlt_w₁).value = .dead := by
      have h : tf₁.locals[w]? = some { mls_w0 with layout := some layW } := by
        cases isMove <;>
          simp [tf₁, tf_u, topFrame₀, deinitFrameLocal, cacheFrameLocalLayout, Ne.symm hwu, hmls_w_eq]
      have h' := Array.getElem?_eq_getElem hlt_w₁
      rw [h] at h'
      have h'' := (Option.some.inj h').symm
      rw [h'']; exact hw_dead_val
    have hforce_dead := annealForceUnionAllocation_dead_err (body := body) (m := m₁) rfl hlt_w₁ hval_w₁
      topFrame.localsIdentity layW
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩) m =
        (m₁, .error (.undefinedBehavior "write to dead local")) := by
      have hpre : Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_4 body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp_u, layU⟩ destPlace) m₁ := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt
        dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
        simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
        apply runRvalue_eq_of_eq
        unfold Miri.Interpreter.evalRvalueIntoPlace
        rw [EStateM.bind_eq_ok hevalPlace']
        dsimp only [translateRvalue]
        have hop_ok' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
            (Miri.Interpreter.OperandPath.rvalue "operand")
            (translateOperand (unionWholeOperand isMove u))
            (some ((annealRvalueHooksLM2_4 body.localDecls body.layouts).placeLayout destPlace)) m₀ =
            .ok ⟨.indirect mp_u, layU⟩ m₁ := hop_ok
        rw [EStateM.bind_eq_ok hop_ok']
        simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2, huse, ↓reduceIte]
      have hmc_dead : annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp_u, layU⟩
          destPlace m₁ = .error (.undefinedBehavior "write to dead local") m₁ := by
        unfold annealMemCopyOp; dsimp only
        rw [EStateM.bind_eq_error hforce_dead]
      rw [hpre]
      unfold Miri.Interpreter.runRvalue
      rw [hmc_dead]
    have ha_ub : evalStmt s ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      have hvld := validateLoadedValue_unionWhole_true hdecl_u hwt isMove
        (.aggregate 0 (unionSlotFields n f (.scalar sc)))
      cases isMove
      · simp only [↓reduceIte, Bool.false_eq_true] at hvld
        have hrv : evalRvalue s.frame.locals (.use (unionWholeOperand false u)) s.memory
            body.localDecls body.layouts =
            .ok (.aggregate 0 (unionSlotFields n f (.scalar sc))) s.frame.locals s.memory := by
          unfold evalRvalue; dsimp only; rw [hbor, hcaller]
          simp only [unionWholeOperand, ↓reduceIte, Bool.false_eq_true, evalOperand,
            hu_slot, readProjectedValue, hvld]
        unfold evalStmt; dsimp only; rw [hrv]; simp [hw_dead]
      · simp only [↓reduceIte] at hvld
        have hrv : evalRvalue s.frame.locals (.use (unionWholeOperand true u)) s.memory
            body.localDecls body.layouts =
            .ok (.aggregate 0 (unionSlotFields n f (.scalar sc)))
              (s.frame.locals.set u .uninit) s.memory := by
          unfold evalRvalue; dsimp only; rw [hbor, hcaller]
          simp only [unionWholeOperand, ↓reduceIte, evalOperand, hu_slot,
            set?_eq_some_set hlt_af_u, hvld]
        have hw1 : get? (s.frame.locals.set u .uninit) w = some .dead := by
          rw [get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hwu), ← get?_eq_getElem?]
          exact hw_dead
        unfold evalStmt; dsimp only; rw [hrv]; simp [hw1]
    rw [hstep_a, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_err]
    exact .ub _ _
  · -- (3) In-place overwrite (`w ≠ u`) of an already memory-backed `UnionMemRel` `_w`.
    intro f f_old f0Ty sc mp_u f0Ty_old sc_old mp_w hwu hf hf_old hu_slot hu_mls hmem_u hw_slot hw_mls hmem_w_old
    obtain ⟨c_u, hmls_u⟩ := hu_mls topFrame hframes
    obtain ⟨c_w, hmls_w⟩ := hw_mls topFrame hframes
    rw [hmls_w] at hmls_w0; injection hmls_w0 with hmls_w0; subst hmls_w0
    obtain ⟨_, mls_u, hlt_af_u, hlt_u, _, hmls_u', _, hloc_u⟩ := hframe.lookup_local hdecl_u
    rw [hmls_u] at hmls_u'; injection hmls_u' with hmls_u'; subst hmls_u'
    have hlt_u₀ : u < topFrame₀.locals.size := by dsimp [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
    have hmls_u₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp_u), c_u⟩ := by
      have h := Array.getElem?_eq_getElem hlt_u₀
      dsimp only [topFrame₀, cacheFrameLocalLayout] at h ⊢
      rw [Array.getElem?_set_ne _ hwu, hmls_u] at h
      exact (Option.some.inj h).symm
    let tf_u := cacheFrameLocalLayout topFrame₀ u hlt_u₀ layU
    have hlt_u' : u < tf_u.locals.size := by dsimp [tf_u]; rw [cacheFrameLocalLayout_size]; exact hlt_u₀
    let tf₁ := if isMove then deinitFrameLocal tf_u u hlt_u' else tf_u
    let m₁ : AnnealStepState := { m with stack := ⟨#[tf₁]⟩ }
    have hop_ok : annealEvalOperandLM2_4 body.localDecls body.layouts
        (translateOperand (unionWholeOperand isMove u)) (some layW) m₀ =
        .ok ⟨.indirect mp_u, layU⟩ m₁ := by
      cases isMove
      · exact annealEvalOperand_copy_live (m := m₀) rfl hlt_u₀ hdecl_u hmls_u₀ hloc_u.layout_eq
      · exact annealEvalOperand_move_live (m := m₀) rfl hlt_u₀ hdecl_u hmls_u₀ hloc_u.layout_eq
    have huse : usesMemCopy ⟨.indirect mp_u, layU⟩ = true := by simp [usesMemCopy, layU, hfields_u]
    have hlt_w₁ : w < tf₁.locals.size := by
      cases isMove <;> simp [tf₁, tf_u, topFrame₀, deinitFrameLocal, cacheFrameLocalLayout_size, hlt_w]
    have hmls_w₁ : tf₁.locals[w]? = some ⟨.live (.indirect mp_w), some layW⟩ := by
      cases isMove <;>
        simp [tf₁, tf_u, topFrame₀, deinitFrameLocal, cacheFrameLocalLayout, Ne.symm hwu, hmls_w_eq]
    have hval_w₁ : (tf₁.locals[w]'hlt_w₁).value = .live (.indirect mp_w) := by
      have h' := Array.getElem?_eq_getElem hlt_w₁
      rw [hmls_w₁] at h'
      exact congrArg Miri.Interpreter.LocalState.value (Option.some.inj h').symm
    cases hmem_u with
    | mk allocId tag_u base_u la_u msc hprov_u _ _ hlive_u hbase_u hptr_u _ hsz_u
        hlen_u _ hp_u _ _ _ hk hmask_u hrel hprim hf0imm hraw_u =>
    cases hmem_w_old with
    | mk destId tag_w base_w la_w _ hprov_w hmis_w hmeta_w hlive_w hbase_w hptr_w hovf_w hsz_w
        hlen_w hmut_w hp_w hal_w hex_w hnat_w _ hmask_w_old _ _ _ _ =>
    have hne_id : allocId ≠ destId := by
      intro hid; subst hid
      have hd := hdisj w u mp_w mp_u c_w c_u hwu hmls_w hmls_u
      rw [hprov_w, hprov_u] at hd; exact hd rfl
    have hbeqf : (allocId == destId) = false := beq_false_of_ne hne_id
    have hlayW_sz : layW.layout.size = translateSizeBytes S := hwt_w.size_eq
    have hsz_nz : (layW.layout.size.bytes == 0) = false := by
      rw [hlayW_sz]
      rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
    obtain ⟨A_w, hcopy_w, hA_sz, hA_len, hA_align, hA_mut, hA_prov, _, hA_mask_pred,
        hA_extra, hA_native, hA_raw⟩ :=
      union_copy_alloc_spec (src := la_u.allocation) (dest := la_w.allocation)
        hS hrel.validBytes hk hlen_u hsz_u hp_u hmask_u hlen_w hsz_w hmut_w hp_w hmask_w_old.len_eq
    have hcopy_w' : Miri.Memory.Allocation.copy la_u.allocation
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO layW.layout.size)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) (allocId == destId) true la_w.allocation =
          .ok () A_w := by
      rw [hlayW_sz, hbeqf]; exact hcopy_w
    obtain ⟨destIdx, _, _, hcopy_ok, _⟩ :=
      annealMemCopyOp_inplaceUnion (body := body) (m := m₁) (wDecl := wDecl) rfl hlt_w₁ hval_w₁
        hnodup hprov_u hlive_u hbase_u hptr_u hprov_w hlive_w hbase_w hptr_w hsz_nz layU
        topFrame.localsIdentity
    obtain ⟨hmemcopy, hnodup', hlive_w', hother_live⟩ := hcopy_ok A_w hcopy_w'
    let mach₃ := inplaceMachine m.machine destIdx destId la_w.kind A_w
    let st₃ : AnnealStepState := { stack := ⟨#[tf₁]⟩, machine := mach₃ }
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩) m =
        (st₃, .ok ()) := by
      have hpre : Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_4 body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp_u, layU⟩ destPlace) m₁ := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt
        dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
        simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
        apply runRvalue_eq_of_eq
        unfold Miri.Interpreter.evalRvalueIntoPlace
        rw [EStateM.bind_eq_ok hevalPlace']
        dsimp only [translateRvalue]
        have hop_ok' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
            (Miri.Interpreter.OperandPath.rvalue "operand")
            (translateOperand (unionWholeOperand isMove u))
            (some ((annealRvalueHooksLM2_4 body.localDecls body.layouts).placeLayout destPlace)) m₀ =
            .ok ⟨.indirect mp_u, layU⟩ m₁ := hop_ok
        rw [EStateM.bind_eq_ok hop_ok']
        simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2, huse, ↓reduceIte]
      rw [hpre]
      unfold Miri.Interpreter.runRvalue
      rw [hmemcopy]
    have htf₁_loc : tf₁.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
      cases isMove <;> exact hframe.location_eq
    have htf₁_body : tf₁.body = topFrame.body := by cases isMove <;> rfl
    have htf₁_rc : tf₁.returnContinuation = topFrame.returnContinuation := by cases isMove <;> rfl
    have htf₁_rp : tf₁.returnPlace = topFrame.returnPlace := by cases isMove <;> rfl
    have htf₁_id : tf₁.localsIdentity = topFrame.localsIdentity := by cases isMove <;> rfl
    have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
      hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl htf₁_loc
    let locals₁ := if isMove then s.frame.locals.set u .uninit else s.frame.locals
    have hlt_af_w₁ : w < locals₁.length := by
      cases isMove <;> simp [locals₁, hlt_af_w]
    have hw_slot₁ : get? locals₁ w =
        some (.init (.aggregate 0 (unionSlotFields n f_old (.scalar sc_old)))) := by
      cases isMove
      · exact hw_slot
      · dsimp [locals₁]
        rw [get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hwu), ← get?_eq_getElem?]
        exact hw_slot
    let locals₂ := locals₁.set w (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))
    have ha_ok : evalStmt s ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩
        body.localDecls body.layouts = MirStepNode.step (advanceStmt s locals₂ s.memory) := by
      have hvld := validateLoadedValue_unionWhole_true hdecl_u hwt isMove
        (.aggregate 0 (unionSlotFields n f (.scalar sc)))
      have hrv : evalRvalue s.frame.locals (.use (unionWholeOperand isMove u)) s.memory
          body.localDecls body.layouts =
          .ok (.aggregate 0 (unionSlotFields n f (.scalar sc))) locals₁ s.memory := by
        unfold evalRvalue; dsimp only; rw [hbor, hcaller]
        cases isMove <;>
          (simp only [↓reduceIte, Bool.false_eq_true] at hvld;
           simp only [unionWholeOperand, ↓reduceIte, Bool.false_eq_true, evalOperand,
             readProjectedValue, hu_slot, set?_eq_some_set hlt_af_u, locals₁, hvld])
      unfold evalStmt; dsimp only; rw [hrv]; simp only []
      rw [hprot, hbor]; dsimp only [invalidateConflictingBorrows]; rw [hmem_same]
      simp [hw_slot₁, set?_eq_some_set hlt_af_w₁, locals₂]
    have hmem_w_new : UnionMemRel mach₃ wDecl.ty body.layouts S f0Ty sc mp_w :=
      .mk destId tag_w base_w ⟨la_w.kind, A_w⟩ msc hprov_w hmis_w hmeta_w hlive_w' hbase_w hptr_w
        hovf_w hA_sz hA_len hA_mut hA_prov (hA_align.trans hal_w) (hA_extra.trans hex_w)
        (hA_native.trans hnat_w) hk hA_mask_pred hrel hprim hf0imm
        (by rw [hA_raw]; exact hraw_u)
    have hframe_u : FrameRelLM2_4 body m.machine { s.frame with locals := locals₁ } tf₁ := by
      have hf_tu : FrameRelLM2_4 body m.machine s.frame tf_u :=
        hframe₀.cache_local_layout hdecl_u hlt_u₀
      cases isMove
      · exact hf_tu
      · have hnew_u : UnionLocalRel m.machine uDecl body.layouts .uninit
            { tf_u.locals[u]'hlt_u' with value := .live (.immediate .uninit) } := by
          have hlay_u : (tf_u.locals[u]'hlt_u').layout = some layU := by
            simp [tf_u, cacheFrameLocalLayout]
          exact .base .uninit _ (.immediate .uninit .uninit _
            (by rw [hlay_u]; intro l hl; exact (Option.some.inj hl).symm) (Or.inl ⟨rfl, rfl⟩))
        exact hf_tu.update_local hdecl_u .uninit (.live (.immediate .uninit)) hnew_u
    have hdisj₁ : MemoryAllocDisjoint tf₁ := by
      have hd_tu : MemoryAllocDisjoint tf_u := hdisj₀.cache_layout hlt_u₀ _
      cases isMove
      · exact hd_tu
      · intro i j mp_i mp_j lay_i lay_j hij hi hj
        simp only [tf₁, deinitFrameLocal, ↓reduceIte] at hi hj
        rw [Array.getElem?_set] at hi hj
        by_cases hi_u : u = i
        · subst hi_u; simp at hi
        · simp only [hi_u, ↓reduceIte] at hi
          by_cases hj_u : u = j
          · subst hj_u; simp at hj
          · simp only [hj_u, ↓reduceIte] at hj
            exact hd_tu i j mp_i mp_j lay_i lay_j hij hi hj
    let tf_fin := { tf₁ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
    let m' : AnnealStepState := { stack := ⟨#[tf_fin]⟩, machine := mach₃ }
    have hframe_fin : FrameRelLM2_4 body mach₃ (advanceStmt s locals₂ s.memory).frame tf_fin :=
      { body_eq := by show tf₁.body = _; rw [htf₁_body]; exact hframe.body_eq
        location_eq := rfl
        af_locals_len := by
          show (locals₁.set w _).length = _
          rw [List.length_set]; exact hframe_u.af_locals_len
        mf_locals_size := hframe_u.mf_locals_size
        locals_rel := by
          intro i decl slot mls hdecl hslot hmls
          have hslot' : get? locals₂ i = some slot := hslot
          have hmls' : tf₁.locals[i]? = some mls := hmls
          rw [get?_eq_getElem?, List.getElem?_set] at hslot'
          by_cases hiw : w = i
          · subst hiw
            simp only [↓reduceIte, hlt_af_w₁, Option.some.injEq] at hslot'
            subst hslot'
            rw [hmls_w₁] at hmls'
            injection hmls' with hmls'
            subst hmls'
            rw [hdecl_w] at hdecl; cases hdecl
            exact .union S n f f0Ty sc mp_w _ (fun l hl => (Option.some.inj hl).symm) hwt_w
              (hty ▸ hfields_u) hf hmem_w_new
          · simp only [hiw, ↓reduceIte] at hslot'
            have hloc := hframe_u.locals_rel i decl slot mls hdecl hslot' hmls'
            refine hloc.of_entry ?_
            intro mp_i c_i hmi a la hpa hla
            subst hmi
            have hne_a : a ≠ destId := by
              intro hae; subst hae
              have hd := hdisj₁ w i mp_w mp_i (some layW) c_i hiw hmls_w₁ hmls'
              rw [hprov_w, hpa] at hd; exact hd rfl
            exact ⟨hother_live a la hne_a hla, rfl⟩ }
    have hstate' : StateRelLM2_4 body (advanceStmt s locals₂ s.memory) m' :=
      StateRelLM2_4.mk tf_fin rfl (by show tf₁.returnContinuation = _; rw [htf₁_rc]; exact hretCont)
        ⟨retLay, by show tf₁.returnPlace = .frameLocal 0 0 none retLay tf₁.localsIdentity
                    rw [htf₁_rp, htf₁_id]; exact hretPlace⟩
        hframe_fin hcal hstack hbor hprot hcaller hdisj₁
    refine ⟨advanceStmt s locals₂ s.memory, m', tf_fin, by rw [hstep_a, ha_ok], hstep_m, hstate',
      ?_, ?_, rfl, ⟨some layW, hmls_w₁⟩, hmem_w_new, hnodup', ?_⟩
    · simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_w₁]
    · dsimp only [advanceStmt, locals₂]
      rw [get?_eq_getElem?, List.getElem?_set_ne hwu]
      cases isMove
      · rwa [← get?_eq_getElem?]
      · dsimp [locals₁]; simp [hlt_af_u]
    · intro _ hw0 _
      obtain ⟨hw', hnext⟩ := MemoryHighWater.inplaceMachine (kind := la_w.kind) (alloc := A_w)
        (allocIdx := destIdx) hw0 hlive_w
      exact ⟨hw', by rw [hnext]; omega⟩

/-- **`step_union_self_copy_overlap_divergence`** (`LM-2.4` `A2` boundary):
self-copy `_u = copy _u` on a `UnionMemRel` union `_u`.

Anneal evaluates `copy _u` to the pure value
`.aggregate 0 (unionSlotFields n f (.scalar sc))` and writes it back into `_u`
(`MirStepNode.step`), whereas `lean-miri` follows
rustc's `copy_op` (`nonoverlapping = true` with `sameAllocation = true` on
identical nonzero byte ranges) and reports
`StepError.undefinedBehavior "whole-value copy between overlapping ranges"`
(`union_copy_self_overlap_err`). Note that self-*move* `_u = move _u` does NOT
overlap in `lean-miri` because `annealEvalOperand` deinitializes `_u` to
`.live (.immediate .uninit)` before `annealForceUnionAllocation` allocates a fresh
stack allocation. -/
theorem step_union_self_copy_overlap_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {u : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩)
    {uDecl : LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals u =
        some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "whole-value copy between overlapping ranges")) := by
  rcases hstate with ⟨topFrame, hframes, _, _, hframe, hcal, _, hbor, hprot, hcaller, _⟩
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot; generalize s.memory = mem; intro hbor hprot; cases mem
    dsimp only at hbor hprot; subst hbor hprot; rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨u, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩ body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
  obtain ⟨c_u, hmls_u⟩ := hu_mls topFrame hframes
  obtain ⟨_, mls_u, hlt_af_u, hlt_u, _, hmls_u', hmls_u_eq, hloc_u⟩ := hframe.lookup_local hdecl_u
  rw [hmls_u] at hmls_u'; injection hmls_u' with hmls_u'; subst hmls_u'
  have ha_ok : evalStmt s ⟨.assign ⟨u, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩
      body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s
        (s.frame.locals.set u (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
        s.memory) := by
    have hvld := validateLoadedValue_unionWhole_true hdecl_u hwt false
      (.aggregate 0 (unionSlotFields n f (.scalar sc)))
    simp only [↓reduceIte, Bool.false_eq_true] at hvld
    have hrv : evalRvalue s.frame.locals (.use (.copy ⟨u, .nil⟩)) s.memory
        body.localDecls body.layouts =
        .ok (.aggregate 0 (unionSlotFields n f (.scalar sc))) s.frame.locals s.memory := by
      unfold evalRvalue; dsimp only; rw [hbor, hcaller]
      simp only [evalOperand, readProjectedValue, hu_slot, hvld]
    unfold evalStmt; dsimp only; rw [hrv]; simp only []
    rw [hprot, hbor]; dsimp only [invalidateConflictingBorrows]; rw [hmem_same]
    simp [hu_slot, set?_eq_some_set hlt_af_u]
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame u hlt_u layU
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 u none topFrame.localsIdentity, layU⟩
  have hevalPlace : annealEvalPlace body.localDecls body.layouts ⟨u, #[]⟩ m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_u hdecl_u (by rw [hmls_u_eq]; exact hloc_u.layout_eq)
  have hlt_u₀ : u < topFrame₀.locals.size := by dsimp [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hmls_u₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp), some layU⟩ := by
    simp [topFrame₀, cacheFrameLocalLayout, hmls_u_eq]
  have hcf := cacheFrameLocalLayout_of_cached topFrame₀ hlt_u₀ (by rw [hmls_u₀])
  have hop : annealEvalOperand body.localDecls body.layouts (.Copy ⟨u, #[]⟩) (some layU) m₀ =
      .ok ⟨.indirect mp, layU⟩ m₀ := by
    have h := annealEvalOperand_copy_live (m := m₀) (known := some layU) rfl hlt_u₀ hdecl_u hmls_u₀
      (fun l hl => (Option.some.inj hl).symm)
    rw [hcf] at h; exact h
  obtain ⟨n', hfields_u, _⟩ := hwt.fields_union
  have hunion_u := isUnionLocal_of_wellTyped hdecl_u hwt
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨u, #[]⟩
      (translateRvalue (.use (.copy ⟨u, .nil⟩))) = true := by
    simp [lm24Assign, lm24Place, hunion_u]
  have huse : usesMemCopy ⟨.indirect mp, layU⟩ = true := by simp [usesMemCopy, layU, hfields_u]
  cases hmem with
  | mk allocId tag baseAddr la _ hprov _ _ hlive hbase hptr _ hsz_u hlen_u hmut_u hp_u _ _ _ hk hmask_u hrel _ _ _ =>
  have hlayU_sz : layU.layout.size = translateSizeBytes S := hwt.size_eq
  have hsz_nz : (layU.layout.size.bytes == 0) = false := by
    rw [hlayU_sz]; rcases hwt.size_valid with rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨_, _, _, _, herr_fn⟩ :=
    annealMemCopyOp_inplaceUnion (body := body) (m := m₀) (wDecl := uDecl) rfl hlt_u₀
      (by rw [hmls_u₀]) hnodup hprov hlive hbase hptr hprov hlive hbase hptr hsz_nz layU
      topFrame.localsIdentity
  obtain ⟨A_err, hcopy_raw⟩ :=
    union_copy_self_overlap_err hwt.size_valid hrel.validBytes hk hlen_u hsz_u hmut_u hp_u hmask_u
  have hcopy_err : Miri.Memory.Allocation.copy la.allocation
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO layU.layout.size)
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) (allocId == allocId) true la.allocation =
        .error .copyRangesOverlap A_err := by
    rw [hlayU_sz, beq_self_eq_true]; exact hcopy_raw
  have hmc_err := herr_fn .copyRangesOverlap A_err hcopy_err
  have hm_err : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨u, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩) m =
      (m₀, .error (.undefinedBehavior "whole-value copy between overlapping ranges")) := by
    have hpre : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp, layU⟩ destPlace) m₀ := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
      simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
      apply runRvalue_eq_of_eq
      unfold Miri.Interpreter.evalRvalueIntoPlace
      have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
          ⟨u, #[]⟩ true m = .ok destPlace m₀ := hevalPlace
      rw [EStateM.bind_eq_ok hevalPlace']
      dsimp only [translateRvalue]
      have hop' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
          (Miri.Interpreter.OperandPath.rvalue "operand")
          (translateOperand (.copy ⟨u, .nil⟩))
          (some ((annealRvalueHooksLM2_4 body.localDecls body.layouts).placeLayout destPlace)) m₀ =
          .ok ⟨.indirect mp, layU⟩ m₀ := hop
      rw [EStateM.bind_eq_ok hop']
      simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2, huse, ↓reduceIte]
    rw [hpre]
    unfold Miri.Interpreter.runRvalue
    rw [hmc_err]
    rfl
  refine ⟨⟨_, by rw [hstep_a, ha_ok], ?_⟩, m₀,
    miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err⟩
  simp [advanceStmt, get?_eq_getElem?, hlt_af_u]

/-- **`step_union_copy_indirect_uninit_divergence`** (`LM-2.4` `A2` boundary —
`MaybeUninit::uninit()` semantics): `_w = copy _u` when `_u` is `.uninit` in
Anneal and already memory-backed with `InitMask.new (translateSizeBytes S) false`
in `lean-miri` (into an uninitialized immediate `_w`).

Anneal's `evalOperand` rejects every read of `.uninit` (`MirStepNode.fail .ub`),
whereas `lean-miri`'s `Allocation.copy` detects `initialized.noBytesInit = true`
and takes its `Allocation.writeUninit` fast path (`union_copy_uninit_alloc_spec`),
succeeding with `(m', .ok true)` and leaving `_w`'s fresh allocation with
`InitMask.new (translateSizeBytes S) false`! -/
theorem step_union_copy_indirect_uninit_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {w u : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩)
    {wDecl uDecl : LocalDecl} (hdecl_w : get? body.localDecls w = some wDecl)
    (hdecl_u : get? body.localDecls u = some uDecl) (hty : wDecl.ty = uDecl.ty)
    {S : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {la_u : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hu_uninit : get? s.frame.locals u = some .uninit)
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp_u), c⟩)
    (hprov_u : mp_u.ptr.provenance = some (.concrete allocId tag))
    (hlive_u : (allocId, la_u) ∈ m.machine.memory.live.toList)
    (hbase_u : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr_u : mp_u.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hlen_u : la_u.allocation.len = S)
    (hsz_u : la_u.allocation.byteSize = translateSizeBytes S)
    (hp_u : la_u.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_u : la_u.allocation.initializationMask =
      Miri.Memory.InitMask.new (translateSizeBytes S) false)
    (hw_uninit : get? s.frame.locals w = some .uninit)
    (hw_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame w) :
    stepMirFn body s = .fail .ub ∧
    ∃ (m' : AnnealStepState)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp_w : Miri.Interpreter.MemPlace AnnealProv) (id : Miri.Memory.AllocId)
      (la_w : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c, tf'.locals[w]? = some ⟨.live (.indirect mp_w), c⟩) ∧
      mp_w.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some id ∧
      (id, la_w) ∈ m'.machine.memory.live.toList ∧
      la_w.allocation.initializationMask =
        Miri.Memory.InitMask.new (translateSizeBytes S) false := by
  rcases hstate with ⟨topFrame, hframes, _, _, hframe, hcal, _, hbor, _, hcaller, _⟩
  obtain ⟨mem', id, hres⟩ := hcanRes
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩ body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
  have ha_ub : evalStmt s ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩
      body.localDecls body.layouts = MirStepNode.fail .ub := by
    unfold evalStmt evalRvalue; dsimp only; rw [hbor, hcaller]
    simp [evalOperand, hu_uninit]
  obtain ⟨c_u, hmls_u⟩ := hu_mls topFrame hframes
  obtain ⟨slot_w, mls_w, _, hlt_w, hslot_w, hmls_w, hmls_w_eq, hloc_w⟩ :=
    hframe.lookup_local hdecl_w
  rw [hw_uninit] at hslot_w; injection hslot_w with hslot_w; subst hslot_w
  have hw_imm' := hw_imm topFrame hframes mls_w hmls_w
  have hwu : w ≠ u := by intro heq; subst heq; exact hw_imm' mp_u (by
    rw [hmls_u] at hmls_w; exact congrArg Miri.Interpreter.LocalState.value (Option.some.inj hmls_w).symm)
  have hloc_w' : LocalRel m.machine wDecl body.layouts .uninit mls_w := by
    cases hloc_w with | base _ _ hl => exact hl
  have hmls_w_val : mls_w.value = .live (.immediate .uninit) := by
    cases hloc_w' with
    | indirect _ mp' _ _ _ _ => exact absurd rfl (hw_imm' mp')
    | immediate _ imm _ _ hv =>
      rcases hv with ⟨_, rfl⟩ | ⟨_, h, _⟩
      · rfl
      · cases h
  obtain ⟨_, mls_u, _, hlt_u, _, hmls_u', _, hloc_u⟩ := hframe.lookup_local hdecl_u
  rw [hmls_u] at hmls_u'; injection hmls_u' with hmls_u'; subst hmls_u'
  have hwt_w : WellTypedUnionTy body.layouts wDecl.ty S := hty ▸ hwt
  have hS := hwt.size_valid
  let layW := translateTy wDecl.ty body.layouts
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame w hlt_w layW
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 w none topFrame.localsIdentity, layW⟩
  have hevalPlace : annealEvalPlace body.localDecls body.layouts ⟨w, #[]⟩ m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_w hdecl_w (by rw [hmls_w_eq]; exact hloc_w'.layout_eq)
  have hlt_u₀ : u < topFrame₀.locals.size := by dsimp [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hmls_u₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp_u), c_u⟩ := by
    have h := Array.getElem?_eq_getElem hlt_u₀
    dsimp only [topFrame₀, cacheFrameLocalLayout] at h ⊢
    rw [Array.getElem?_set_ne _ hwu, hmls_u] at h
    exact (Option.some.inj h).symm
  let topFrame₁ := cacheFrameLocalLayout topFrame₀ u hlt_u₀ layU
  let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
  have hop : annealEvalOperand body.localDecls body.layouts (.Copy ⟨u, #[]⟩) (some layW) m₀ =
      .ok ⟨.indirect mp_u, layU⟩ m₁ :=
    annealEvalOperand_copy_live (m := m₀) rfl hlt_u₀ hdecl_u hmls_u₀ hloc_u.layout_eq
  have hlt_w₁ : w < topFrame₁.locals.size := by
    dsimp [topFrame₁, topFrame₀]; rw [cacheFrameLocalLayout_size, cacheFrameLocalLayout_size]; exact hlt_w
  have hmls_w₁ : topFrame₁.locals[w]'hlt_w₁ = { mls_w with layout := some layW } := by
    have h := Array.getElem?_eq_getElem hlt_w₁
    have h' : topFrame₁.locals[w]? = some { mls_w with layout := some layW } := by
      dsimp [topFrame₁, topFrame₀, cacheFrameLocalLayout]
      simp [Ne.symm hwu, hmls_w_eq]
    rw [h'] at h; exact (Option.some.inj h).symm
  obtain ⟨alloc, htry, hbs, hlen_a, _, hmut, _, hprov_alloc, hmask_alloc⟩ :=
    freshUnionAlloc_spec layW.layout.size layW.layout.align.abi (translateTy_align_pow2_le_29 _ _)
  have hlayW_sz : layW.layout.size = translateSizeBytes S := hwt_w.size_eq
  obtain ⟨A_w, hcopy_w, _, _, _, _, _, hA_mask, _⟩ :=
    union_copy_uninit_alloc_spec (src := la_u.allocation)
      (dest := alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree))
      hS false hlen_u hsz_u hp_u hmask_u
      (by show alloc.len = S; rw [hlen_a, hlayW_sz]; exact translateSizeBytes_toNat_of_valid hS)
      (by show alloc.byteSize = translateSizeBytes S; rw [hbs, hlayW_sz])
      hmut hprov_alloc
      (by show alloc.initializationMask.len = translateSizeBytes S; rw [hmask_alloc, hlayW_sz]; rfl)
  have hcopy_w' : Miri.Memory.Allocation.copy la_u.allocation
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO layW.layout.size)
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true (alloc.withExtra none) =
        .ok () A_w := by
    rw [hlayW_sz]; exact hcopy_w
  have hmemcopy := annealMemCopyOp_freshUnion (body := body) (m := m₁) rfl hlt_w₁ hdecl_w
    (by rw [hmls_w₁]) (by rw [hmls_w₁]; exact hmls_w_val) hwt_w.sized htry hres hnodup
    hprov_u hlive_u hbase_u hptr_u hcopy_w' layU topFrame.localsIdentity
  obtain ⟨n, hfields_u, _⟩ := hwt.fields_union
  have hunion_w := isUnionLocal_of_wellTyped hdecl_w hwt_w
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨w, #[]⟩
      (translateRvalue (.use (.copy ⟨u, .nil⟩))) = true := by
    simp [lm24Assign, lm24Place, hunion_w]
  have huse : usesMemCopy ⟨.indirect mp_u, layU⟩ = true := by simp [usesMemCopy, layU, hfields_u]
  let tf₃ := setFrameLocalIndirect topFrame₁ w hlt_w₁ (stackAllocPlace id)
  let st₃ : AnnealStepState := { stack := ⟨#[tf₃]⟩, machine := stackAllocMachine m.machine mem' id A_w }
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩) m = (st₃, .ok ()) := by
    have hpre : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp_u, layU⟩ destPlace) m₁ := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
      simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
      apply runRvalue_eq_of_eq
      unfold Miri.Interpreter.evalRvalueIntoPlace
      have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
          ⟨w, #[]⟩ true m = .ok destPlace m₀ := hevalPlace
      rw [EStateM.bind_eq_ok hevalPlace']
      dsimp only [translateRvalue]
      have hop' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
          (Miri.Interpreter.OperandPath.rvalue "operand")
          (translateOperand (.copy ⟨u, .nil⟩))
          (some ((annealRvalueHooksLM2_4 body.localDecls body.layouts).placeLayout destPlace)) m₀ =
          .ok ⟨.indirect mp_u, layU⟩ m₁ := hop
      rw [EStateM.bind_eq_ok hop']
      simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2, huse, ↓reduceIte]
    rw [hpre]
    unfold Miri.Interpreter.runRvalue
    rw [hmemcopy]
  have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
    hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl hframe.location_eq
  refine ⟨by rw [hstep_a, ha_ub], _,
    { tf₃ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ },
    stackAllocPlace id, id, ⟨.stack, A_w⟩, hstep_m, rfl, ⟨(topFrame₁.locals[w]'hlt_w₁).layout, ?_⟩,
    rfl, by simp [st₃, stackAllocMachine], hA_mask⟩
  simp [tf₃, setFrameLocalIndirect]

/-- `annealUnionAggregateField` on a `.dead` destination local `u` fails with
`StepError.undefinedBehavior "write to dead local"`. -/
theorem annealUnionAggregateField_dead_err
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {u : Nat} (hlt : u < tf.locals.size)
    (hdead : (tf.locals[u]'hlt).value = .dead)
    (ident : Miri.Interpreter.LocalsIdentity) (lay : Miri.Interpreter.LocalLayout)
    (f : Nat) :
    annealUnionAggregateField body.localDecls body.layouts ⟨.local 0 u none ident, lay⟩ f m =
      .error (.undefinedBehavior "write to dead local") m := by
  unfold annealUnionAggregateField
  rw [EStateM.bind_eq_error (annealForceUnionAllocation_dead_err hframes hlt hdead ident lay)]

/-- `annealUnionAggregateField` on an already memory-backed union local `u`
(`mp.metadata = .none`) reuses `mp` in place without allocating. -/
theorem annealUnionAggregateField_inplace
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {u : Nat} {uDecl : LocalDecl}
    (hlt : u < tf.locals.size)
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hval : (tf.locals[u]'hlt).value = .live (.indirect mp))
    (hmeta : mp.metadata = .none)
    {n f : Nat}
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl)
    (hfl_sized : fl.layout.isSized = true)
    (ident : Miri.Interpreter.LocalsIdentity) :
    annealUnionAggregateField body.localDecls body.layouts
        ⟨.local 0 u none ident, translateTy uDecl.ty body.layouts⟩ f m =
      .ok ⟨.memory mp, fl⟩ m := by
  have hforce := annealForceUnionAllocation_indirect_eq (body := body) hframes hlt hval ident
    (translateTy uDecl.ty body.layouts)
  have hproj := projectField_unionAggregate tf body.layouts m.machine hfields hf hfl hfl_sized hmeta
  unfold annealUnionAggregateField
  simp only [bind, EStateM.bind, hforce, get, getThe, MonadStateOf.get, EStateM.get,
    stack_currentFrame?_singleton m.stack tf hframes, hproj, pure, EStateM.pure]

/-- **`step_union_aggregate_overwrite_simulation`** (`LM-2.4` `A2` + `D13a`):
statement-level simulation for `_u = U { field_f: op }`
(`Rvalue.aggregate (.adt d 0 (some f)) [op]` for ANY `f < n`) across:
1. `.dead` destination `_u`: UB in both machines (`StepRelLM2_4.ub`).
2. Already memory-backed `UnionMemRel` destination `_u` (`sc_old` of width
   `sc_old.sizeBytes ≤ (translateTy f0Ty body.layouts).layout.size.bytes.toNat ≤ S`):
   UB in both if `op` reads a dead/uninitialized local, and otherwise lockstep
   in-place overwrite (`StateRelLM2_4` + `StepPreservesHighWater m 0`) expanding
   or preserving the initialized prefix `[0, sc.sizeBytes)` while keeping
   `[sc.sizeBytes, S)` uninitialized. -/
theorem step_union_aggregate_overwrite_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {u : Local} {d : DefPath} {f : Nat} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩)
    {uDecl : LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {S n : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl)
    (hfl_sized : fl.layout.isSized = true)
    {f0Ty : Ty} (hprim0 : IsPrimScalarTy f0Ty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op f0Ty)
    (hf0_le : (translateTy f0Ty body.layouts).layout.size.bytes.toNat ≤ S)
    (hadt : ∃ args, uDecl.ty.kind = .adt d args := by exact ⟨_, rfl⟩)
    (hfl_sz : fl.layout.size = (translateTy f0Ty body.layouts).layout.size := by rfl)
    (hdecls_adt : ∀ l ∈ collectAdtLayoutsInDecls body.layouts d body.localDecls,
      body.layouts.lookup uDecl.ty.layoutIdx = some l := by
        simp [collectAdtLayoutsInDecls, collectAdtLayoutsInTyAux, stringEq,
          LayoutTable.lookup, get?]) :
    (get? s.frame.locals u = some .dead →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ f_old f0Ty_old sc_old mp,
      f_old < n →
      get? s.frame.locals u =
        some (.init (.aggregate 0 (unionSlotFields n f_old (.scalar sc_old)))) →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩) →
      UnionMemRel m.machine uDecl.ty body.layouts S f0Ty_old sc_old mp →
      sc_old.sizeBytes ≤ (translateTy f0Ty body.layouts).layout.size.bytes.toNat →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
      (∀ s', stepMirFn body s = .step s' →
        ∃ (sc : MirAst.ScalarInt) (m' : AnnealStepState)
          (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
          Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
            (m', .ok true) ∧
          StateRelLM2_4 body s' m' ∧
          get? s'.frame.locals u =
            some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) ∧
          m'.stack.frames = #[tf'] ∧
          (∃ c, tf'.locals[u]? = some ⟨.live (.indirect mp), c⟩) ∧
          UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty sc mp ∧
          LiveAllocsNodup m'.machine ∧
          StepPreservesHighWater m 0 (m', .ok true))) := by
  rcases hstate with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have hop_tf := hop topFrame hframes
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot; generalize s.memory = mem; intro hbor hprot; cases mem
    dsimp only at hbor hprot; subst hbor hprot; rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩
      body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
  obtain ⟨slot_u, mls_u, hlt_af_u, hlt_u, hslot_u, hmls_u, hmls_u_eq, hloc_u⟩ :=
    hframe.lookup_local hdecl_u
  let lay := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame u hlt_u lay
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 u none topFrame.localsIdentity, lay⟩
  have hevalPlace : annealEvalPlace body.localDecls body.layouts ⟨u, #[]⟩ m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_u hdecl_u (by rw [hmls_u_eq]; exact hloc_u.layout_eq)
  have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
      ⟨u, #[]⟩ true m = .ok destPlace m₀ := hevalPlace
  have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
  have hunionLay : isUnionLayout destPlace.layout = true := by
    simp only [destPlace, isUnionLayout, lay, hfields]
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨u, #[]⟩
      (translateRvalue (.aggregate (.adt d 0 (some f)) [op])) = true := by
    simp [lm24Assign, lm24Place, hunion]
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.writeAggregate (annealAggregateHooksLM2_4 body.localDecls body.layouts) ()
          (.Adt 0 0 #[] none (some f)) #[translateOperand op] destPlace) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    dsimp only [translateRvalue, translateAggregateKind, List.map, List.toArray]
    rw [evalRvalueIntoPlace_aggregate_def]
    exact EStateM.bind_eq_ok hevalPlace'
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hframe₀ : FrameRelLM2_4 body m.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_u hlt_u
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ := hdisj.cache_layout hlt_u lay
  have hop₀ : WellTypedScalarOperand body topFrame₀ op f0Ty := hop_tf.cache_layout hlt_u lay
  have hrv_spec := evalRvalue_unionAggregate_activeField_eq (locals := s.frame.locals) hbor hcaller
    hdecl_u hadt hwt hfields hf hfl hprim0 hfl_sz hop_tf hdecls_adt
  refine ⟨?_, ?_⟩
  · -- (1) Dead destination `_u`.
    intro hu_dead
    rw [hu_dead] at hslot_u; injection hslot_u with hslot_u; subst hslot_u
    have hdead_val := hloc_u.dead_value
    have hm0_dead : (topFrame₀.locals[u]'hlt_u₀).value = .dead := by
      simp [topFrame₀, cacheFrameLocalLayout, hmls_u_eq, hdead_val]
    have hf_dead := annealUnionAggregateField_dead_err (body := body) (m := m₀) rfl hlt_u₀ hm0_dead
      topFrame.localsIdentity lay f
    have hwa_err : Miri.Interpreter.writeAggregate
        (annealAggregateHooksLM2_4 body.localDecls body.layouts) ()
        (.Adt 0 0 #[] none (some f)) #[translateOperand op] destPlace m₀ =
        .error (.undefinedBehavior "write to dead local") m₀ := by
      rw [writeAggregate_union_def]
      simp only [aggLM2_4_projectDowncast, hunionLay, ↓reduceIte, beq_self_eq_true,
        aggLM2_4_projectField, pure]
      dsimp only [bind, EStateM.bind, EStateM.pure]
      simp only [hunionLay, ↓reduceIte]
      rw [hf_dead]
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩) m =
        (m₀, .error (.undefinedBehavior "write to dead local")) := by
      rw [hm_eval]; unfold Miri.Interpreter.runRvalue; rw [hwa_err]
    have ha_ub : evalStmt s ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      rcases evalScalarOperand_LM2_4 hframe₀ hprim0 hop₀ s.memory.globals (some fl) with
        ⟨ha_op_ub, _⟩ | ⟨sc, msc, _, ha_op_ok, _, _, _, _, _, _, _, himm'⟩
      · have hrv := hrv_spec.1 ha_op_ub
        unfold evalStmt; dsimp only; rw [hrv]
      · have hrv := hrv_spec.2 sc msc ha_op_ok himm'
        unfold evalStmt; dsimp only; rw [hrv]; simp [hu_dead]
    rw [hstep_a, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_stmt]
    exact .ub _ _
  · -- (2) Already memory-backed `UnionMemRel` destination `_u`.
    intro f_old f0Ty_old sc_old mp _ hu_slot hu_mls hmem_old hk_ge_ty
    obtain ⟨c_u, hmls_u'⟩ := hu_mls topFrame hframes
    rw [hmls_u'] at hmls_u; injection hmls_u with hmls_u; subst hmls_u
    have hm0_val : (topFrame₀.locals[u]'hlt_u₀).value = .live (.indirect mp) := by
      simp [topFrame₀, cacheFrameLocalLayout, hmls_u_eq]
    have hmeta : mp.metadata = .none := by
      cases hmem_old with | mk _ _ _ _ _ _ _ hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact hm
    have hfield : annealUnionAggregateField body.localDecls body.layouts destPlace f m₀ =
        .ok ⟨.memory mp, fl⟩ m₀ :=
      annealUnionAggregateField_inplace (body := body) (m := m₀) rfl hlt_u₀ hm0_val hmeta
        hfields hf hfl hfl_sized topFrame.localsIdentity
    have hwa_pre : ∀ (k : Miri.Interpreter.RvalueM AnnealStepState Unit),
        (do
          let variantDest ← (annealAggregateHooksLM2_4 body.localDecls body.layouts).projectDowncast ()
            destPlace 0
          let field ← (annealAggregateHooksLM2_4 body.localDecls body.layouts).projectField ()
            variantDest f
          let operand ← (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
            (Miri.Interpreter.OperandPath.aggregate 0) (translateOperand op)
            (some ((annealAggregateHooksLM2_4 body.localDecls body.layouts).placeLayout field))
          (annealAggregateHooksLM2_4 body.localDecls body.layouts).copyOpNoValidate () operand
            field false
          k) m₀ =
        (do
          let operand ← (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
            (Miri.Interpreter.OperandPath.aggregate 0) (translateOperand op) (some fl)
          (annealAggregateHooksLM2_4 body.localDecls body.layouts).copyOpNoValidate () operand
            ⟨.memory mp, fl⟩ false
          k) m₀ := by
      intro k
      simp only [aggLM2_4_projectDowncast, hunionLay, ↓reduceIte, beq_self_eq_true,
        aggLM2_4_projectField, bind, EStateM.bind, pure, EStateM.pure, hfield]
      rfl
    have hlm_op_eq : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        (some fl) = annealEvalOperand body.localDecls body.layouts (translateOperand op) (some fl) := by
      funext st; rw [annealEvalOperandLM2_4_scalar hop₀]
    rcases evalScalarOperand_LM2_4 hframe₀ hprim0 hop₀ s.memory.globals (some fl) with
      ⟨ha_ub, ⟨m_err, msg, hm_err⟩ | ⟨lay_op, st', hm_uninit⟩⟩ |
      ⟨sc, msc, tf₁, ha_ok, hm_ok, hframe₁, hdisj₁, _, htf₁, hind₁, hrel', himm'⟩
    · have ha : evalStmt s ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        have hrv := hrv_spec.1 ha_ub
        unfold evalStmt; dsimp only; rw [hrv]
      have hev_err : (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
          (Miri.Interpreter.OperandPath.aggregate 0) (translateOperand op) (some fl) m₀ =
          .error (.undefinedBehavior msg) m_err := by
        show (do let opTy ← annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) (some fl)
                 let imm ← annealReadImmediateLM2_2 opTy
                 return (⟨.immediate imm.imm, imm.layout⟩ : Miri.Interpreter.OpTy AnnealProv)) m₀ = _
        rw [hlm_op_eq, EStateM.bind_eq_error hm_err]
      have hwa : Miri.Interpreter.writeAggregate
          (annealAggregateHooksLM2_4 body.localDecls body.layouts) ()
          (.Adt 0 0 #[] none (some f)) #[translateOperand op] destPlace m₀ =
          .error (.undefinedBehavior msg) m_err := by
        rw [writeAggregate_union_def, hwa_pre, EStateM.bind_eq_error hev_err]
      have hm_stmt : Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_4 body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩) m =
          (m_err, .error (.undefinedBehavior msg)) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue; rw [hwa]
      rw [hstep_a, ha, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
        hbb hstmt hm_stmt]
      exact ⟨.ub _ _, fun _ h => absurd h MirStepNode_fail_ne_step⟩
    · have ha : evalStmt s ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        have hrv := hrv_spec.1 ha_ub
        unfold evalStmt; dsimp only; rw [hrv]
      have hev_err : (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
          (Miri.Interpreter.OperandPath.aggregate 0) (translateOperand op) (some fl) m₀ =
          .error (.undefinedBehavior "read of uninitialized local") st' := by
        show (do let opTy ← annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) (some fl)
                 let imm ← annealReadImmediateLM2_2 opTy
                 return (⟨.immediate imm.imm, imm.layout⟩ : Miri.Interpreter.OpTy AnnealProv)) m₀ = _
        rw [hlm_op_eq, EStateM.bind_eq_ok hm_uninit]; rfl
      have hwa : Miri.Interpreter.writeAggregate
          (annealAggregateHooksLM2_4 body.localDecls body.layouts) ()
          (.Adt 0 0 #[] none (some f)) #[translateOperand op] destPlace m₀ =
          .error (.undefinedBehavior "read of uninitialized local") st' := by
        rw [writeAggregate_union_def, hwa_pre, EStateM.bind_eq_error hev_err]
      have hm_stmt : Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_4 body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩) m =
          (st', .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue; rw [hwa]
      rw [hstep_a, ha, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
        hbb hstmt hm_stmt]
      exact ⟨.ub _ _, fun _ h => absurd h MirStepNode_fail_ne_step⟩
    · -- Operand succeeds: rewrite `[0, sc.sizeBytes)` in place.
      obtain ⟨hsz_k, hkv⟩ : (translateTy f0Ty body.layouts).layout.size =
          translateSizeBytes sc.sizeBytes ∧ ValidScalarBytes sc.sizeBytes := by
        cases himm' with | scalar _ _ hr hsz _ _ => exact ⟨hsz, hr.validBytes⟩
      have hk_toNat : (translateTy f0Ty body.layouts).layout.size.bytes.toNat = sc.sizeBytes := by
        rw [hsz_k]; exact translateSizeBytes_toNat_of_valid hkv
      have hk_ge : sc_old.sizeBytes ≤ sc.sizeBytes := by rw [← hk_toNat]; exact hk_ge_ty
      have hk_le : sc.sizeBytes ≤ S := by rw [← hk_toNat]; exact hf0_le
      obtain ⟨allocIdx, allocId, kind, A', la₀, hprov_a, hlive₀, hw, hmem', hnodup', hother⟩ :=
        annealWriteImmediate_unionInplace_ge (tf := tf₁) (destLay := fl) hnodup hmem_old
          hwt.size_valid hprim0 hrel' hk_ge hk_le himm'
      let mach₃ := inplaceMachine m.machine allocIdx allocId kind A'
      let st₃ : AnnealStepState := { stack := ⟨#[tf₁]⟩, machine := mach₃ }
      have hev_ok : (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
          (Miri.Interpreter.OperandPath.aggregate 0) (translateOperand op) (some fl) m₀ =
          .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy f0Ty body.layouts⟩
            { stack := ⟨#[tf₁]⟩, machine := m.machine } := by
        show (do let opTy ← annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) (some fl)
                 let imm ← annealReadImmediateLM2_2 opTy
                 return (⟨.immediate imm.imm, imm.layout⟩ : Miri.Interpreter.OpTy AnnealProv)) m₀ = _
        rw [hlm_op_eq, EStateM.bind_eq_ok hm_ok]; rfl
      have hcopy : (annealAggregateHooksLM2_4 body.localDecls body.layouts).copyOpNoValidate ()
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy f0Ty body.layouts⟩
          ⟨.memory mp, fl⟩ false { stack := ⟨#[tf₁]⟩, machine := m.machine } = .ok () st₃ := by
        rw [aggLM2_4_copyOpNoValidate]
        simp only [bind, EStateM.bind, annealReadImmediateLM2_2, pure, EStateM.pure]
        exact hw
      have hu₀ : topFrame₀.locals[u]? = some ⟨.live (.indirect mp), some lay⟩ := by
        dsimp only [topFrame₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set_self]; simp [hmls_u_eq]
      have hu₁ : tf₁.locals[u]? = some ⟨.live (.indirect mp), some lay⟩ := by
        rw [hind₁ u mp (some lay) hu₀, hu₀]
      have hlt₁ : u < tf₁.locals.size := by
        rw [hframe₁.mf_locals_size, ← hframe.mf_locals_size]; exact hlt_u
      have hu₁_val : (tf₁.locals[u]'hlt₁).value = .live (.indirect mp) := by
        have h := Array.getElem?_eq_getElem hlt₁
        rw [hu₁] at h; exact congrArg Miri.Interpreter.LocalState.value (Option.some.inj h).symm
      have htf₁_id : tf₁.localsIdentity = topFrame.localsIdentity := by rw [htf₁]; rfl
      have hdisc : (annealAggregateHooksLM2_4 body.localDecls body.layouts).writeDiscriminant () 0
          destPlace st₃ = .ok () st₃ := by
        rw [aggLM2_4_writeDiscriminant]
        have hens : annealEnsureAllocated destPlace st₃ = .ok mp st₃ := by
          dsimp only [destPlace]; rw [← htf₁_id]
          exact annealEnsureAllocated_indirect rfl hlt₁ hu₁_val
        rw [EStateM.bind_eq_ok hens]; rfl
      have hwa : Miri.Interpreter.writeAggregate
          (annealAggregateHooksLM2_4 body.localDecls body.layouts) ()
          (.Adt 0 0 #[] none (some f)) #[translateOperand op] destPlace m₀ = .ok () st₃ := by
        rw [writeAggregate_union_def, hwa_pre, EStateM.bind_eq_ok hev_ok, EStateM.bind_eq_ok hcopy,
          EStateM.bind_eq_ok hdisc]
        rfl
      have hm_stmt : Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_4 body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩) m =
          (st₃, .ok ()) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue; rw [hwa]
      have htf₁_loc : tf₁.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
        rw [htf₁]; exact hframe.location_eq
      have htf₁_body : tf₁.body = topFrame.body := by rw [htf₁]; rfl
      have htf₁_rc : tf₁.returnContinuation = topFrame.returnContinuation := by rw [htf₁]; rfl
      have htf₁_rp : tf₁.returnPlace = topFrame.returnPlace := by rw [htf₁]; rfl
      have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
        hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl htf₁_loc
      let locals₂ :=
        s.frame.locals.set u (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))
      have ha_ok' : evalStmt s ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩
          body.localDecls body.layouts = MirStepNode.step (advanceStmt s locals₂ s.memory) := by
        have hrv := hrv_spec.2 sc msc ha_ok himm'
        unfold evalStmt; dsimp only; rw [hrv]; simp only []
        rw [hprot, hbor]; dsimp only [invalidateConflictingBorrows]; rw [hmem_same]
        simp [hu_slot, set?_eq_some_set hlt_af_u, locals₂]
      have hdisj₁' := hdisj₁ hdisj₀
      let tf_fin := { tf₁ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
      let m' : AnnealStepState := { stack := ⟨#[tf_fin]⟩, machine := mach₃ }
      have hframe_fin : FrameRelLM2_4 body mach₃ (advanceStmt s locals₂ s.memory).frame tf_fin :=
        { body_eq := by show tf₁.body = _; rw [htf₁_body]; exact hframe.body_eq
          location_eq := rfl
          af_locals_len := by show (s.frame.locals.set u _).length = _; rw [List.length_set]; exact hframe.af_locals_len
          mf_locals_size := hframe₁.mf_locals_size
          locals_rel := by
            intro i decl slot mls hdecl hslot hmls
            have hslot' : get? locals₂ i = some slot := hslot
            have hmls' : tf₁.locals[i]? = some mls := hmls
            rw [get?_eq_getElem?, List.getElem?_set] at hslot'
            by_cases hiu : u = i
            · subst hiu
              simp only [↓reduceIte, hlt_af_u, Option.some.injEq] at hslot'
              subst hslot'
              rw [hu₁] at hmls'; injection hmls' with hmls'; subst hmls'
              rw [hdecl_u] at hdecl; cases hdecl
              exact .union S n f f0Ty sc mp _ (fun l hl => (Option.some.inj hl).symm) hwt hfields
                hf hmem'
            · simp only [hiu, ↓reduceIte] at hslot'
              have hloc := hframe₁.locals_rel i decl slot mls hdecl hslot' hmls'
              refine hloc.of_entry ?_
              intro mp_i c_i hmi a la hpa hla
              subst hmi
              have hne_a : a ≠ allocId := by
                intro hae; subst hae
                have hd := hdisj₁' u i mp mp_i (some lay) c_i hiu hu₁ hmls'
                rw [hprov_a, hpa] at hd; exact hd rfl
              exact ⟨hother a la hne_a hla, rfl⟩ }
      have hstate' : StateRelLM2_4 body (advanceStmt s locals₂ s.memory) m' :=
        StateRelLM2_4.mk tf_fin rfl (by show tf₁.returnContinuation = _; rw [htf₁_rc]; exact hretCont)
          ⟨retLay, by show tf₁.returnPlace = .frameLocal 0 0 none retLay tf₁.localsIdentity
                      rw [htf₁_rp, htf₁_id]; exact hretPlace⟩
          hframe_fin hcal hstack hbor hprot hcaller hdisj₁'
      rw [hstep_a, ha_ok', hstep_m]
      refine ⟨.step _ _ hstate', fun s' hs' => ?_⟩
      have hs'' := MirStepNode_step_inj hs'
      subst hs''
      refine ⟨sc, m', tf_fin, rfl, hstate', ?_, rfl, ⟨some lay, hu₁⟩, hmem', hnodup', ?_⟩
      · simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_u]
      · intro _ hw0 _
        obtain ⟨hw', hnext⟩ := MemoryHighWater.inplaceMachine (kind := kind) (alloc := A')
          (allocIdx := allocIdx) hw0 hlive₀
        exact ⟨hw', by rw [hnext]; omega⟩

/-- **`step_union_aggregate_smaller_overwrite_divergence`** (`LM-2.4` `A2`
boundary — `I-11` raw-byte retention across narrower unprojected union aggregate
writes): when `_u` already holds a wider scalar `sc_old` (`UnionMemRel` with
`IsUnionPrefixMask S sc_old.sizeBytes`) and unprojected `_u = U { field_f: op }`
overwrites `_u` with a *narrower* scalar `sc` (`sc.sizeBytes < sc_old.sizeBytes ≤ S`),
Anneal evaluates `evalRvalue` independently of `dst` (`Statements.lean` unprojected
`.assign`) and replaces `_u` with `.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))`
(forgetting the trailing bytes `[sc.sizeBytes, sc_old.sizeBytes)`), whereas
`lean-miri`'s destination-passing `evalRvalueIntoPlace` writes `sc` into
`[0, sc.sizeBytes)` in place **without** deinitializing `[sc.sizeBytes, sc_old.sizeBytes)`:
1. `IsUnionPrefixMask S sc_old.sizeBytes A'.initializationMask` still holds
   (the wider `sc_old.sizeBytes` prefix remains initialized),
2. `A'.readScalar` on `[0, sc.sizeBytes)` decodes `sc`, and
3. `(unionAllocRaw A').extract sc.sizeBytes S = (unionAllocRaw la_old.allocation).extract sc.sizeBytes S`
   (all trailing bytes `[sc.sizeBytes, S)`, including `sc_old`'s high bytes
   `[sc.sizeBytes, sc_old.sizeBytes)`, are preserved verbatim!). -/
theorem step_union_aggregate_smaller_overwrite_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {u : Local} {d : DefPath} {f : Nat} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩)
    {uDecl : LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {S n f_old : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl)
    (hfl_sized : fl.layout.isSized = true)
    {f0Ty_old f0Ty : Ty} {sc_old : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f_old (.scalar sc_old)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag}
    {la_old : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hlive_old : (allocId, la_old) ∈ m.machine.memory.live.toList)
    (hmem_old : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty_old sc_old mp)
    (hprim0 : IsPrimScalarTy f0Ty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op f0Ty)
    (hlt_width : (translateTy f0Ty body.layouts).layout.size.bytes.toNat < sc_old.sizeBytes)
    {sc : MirAst.ScalarInt}
    (hop_ok : evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
      .ok (.scalar sc) s.frame.locals)
    (hadt : ∃ args, uDecl.ty.kind = .adt d args := by exact ⟨_, rfl⟩)
    (hfl_sz : fl.layout.size = (translateTy f0Ty body.layouts).layout.size := by rfl)
    (hdecls_adt : ∀ l ∈ collectAdtLayoutsInDecls body.layouts d body.localDecls,
      body.layouts.lookup uDecl.ty.layoutIdx = some l := by
        simp [collectAdtLayoutsInDecls, collectAdtLayoutsInTyAux, stringEq,
          LayoutTable.lookup, get?]) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals u =
        some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))) ∧
    ∃ (m' : AnnealStepState) (msc : Miri.Memory.ScalarInt)
      (A' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      ScalarRel sc msc ∧
      (allocId, ⟨la_old.kind, A'⟩) ∈ m'.machine.memory.live.toList ∧
      IsUnionPrefixMask S sc_old.sizeBytes A'.initializationMask ∧
      A'.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
          .ok (.fromScalarInt msc) ∧
      (unionAllocRaw A').extract sc.sizeBytes S =
        (unionAllocRaw la_old.allocation).extract sc.sizeBytes S := by
  rcases hstate with ⟨topFrame, hframes, _, _, hframe, hcal, _, hbor, hprot, hcaller, _⟩
  have hop_tf := hop topFrame hframes
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot; generalize s.memory = mem; intro hbor hprot; cases mem
    dsimp only at hbor hprot; subst hbor hprot; rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩
      body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
  obtain ⟨c_u, hmls_u'⟩ := hu_mls topFrame hframes
  obtain ⟨_, mls_u, hlt_af_u, hlt_u, _, hmls_u, hmls_u_eq, hloc_u⟩ := hframe.lookup_local hdecl_u
  rw [hmls_u'] at hmls_u; injection hmls_u with hmls_u; subst hmls_u
  let lay := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame u hlt_u lay
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 u none topFrame.localsIdentity, lay⟩
  have hevalPlace : annealEvalPlace body.localDecls body.layouts ⟨u, #[]⟩ m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_u hdecl_u (by rw [hmls_u_eq]; exact hloc_u.layout_eq)
  have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
      ⟨u, #[]⟩ true m = .ok destPlace m₀ := hevalPlace
  have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
  have hunionLay : isUnionLayout destPlace.layout = true := by
    simp only [destPlace, isUnionLayout, lay, hfields]
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨u, #[]⟩
      (translateRvalue (.aggregate (.adt d 0 (some f)) [op])) = true := by
    simp [lm24Assign, lm24Place, hunion]
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.writeAggregate (annealAggregateHooksLM2_4 body.localDecls body.layouts) ()
          (.Adt 0 0 #[] none (some f)) #[translateOperand op] destPlace) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    dsimp only [translateRvalue, translateAggregateKind, List.map, List.toArray]
    rw [evalRvalueIntoPlace_aggregate_def]
    exact EStateM.bind_eq_ok hevalPlace'
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hm0_val : (topFrame₀.locals[u]'hlt_u₀).value = .live (.indirect mp) := by
    simp [topFrame₀, cacheFrameLocalLayout, hmls_u_eq]
  cases hmem_old with
  | mk allocId' tag' baseAddr' la' _ hprov' _ hmeta hlive' hbase hptr _ hsz_old hlen_old hmut_old
      hp_old _ _ _ hk_old hmask_old hrel_old _ _ _ =>
  have hid_eq : allocId' = allocId := by rw [hprov] at hprov'; injection hprov' with hc; cases hc; rfl
  subst allocId'
  have hla_eq : la' = la_old := by
    have h1 := array_find?_of_nodup_fst hnodup hlive'
    have h2 := array_find?_of_nodup_fst hnodup hlive_old
    rw [h1] at h2; exact Prod.mk.inj (Option.some.inj h2) |>.2
  subst la'
  have hfield : annealUnionAggregateField body.localDecls body.layouts destPlace f m₀ =
      .ok ⟨.memory mp, fl⟩ m₀ :=
    annealUnionAggregateField_inplace (body := body) (m := m₀) rfl hlt_u₀ hm0_val hmeta
      hfields hf hfl hfl_sized topFrame.localsIdentity
  have hwa_pre : ∀ (k : Miri.Interpreter.RvalueM AnnealStepState Unit),
      (do
        let variantDest ← (annealAggregateHooksLM2_4 body.localDecls body.layouts).projectDowncast ()
          destPlace 0
        let field ← (annealAggregateHooksLM2_4 body.localDecls body.layouts).projectField ()
          variantDest f
        let operand ← (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
          (Miri.Interpreter.OperandPath.aggregate 0) (translateOperand op)
          (some ((annealAggregateHooksLM2_4 body.localDecls body.layouts).placeLayout field))
        (annealAggregateHooksLM2_4 body.localDecls body.layouts).copyOpNoValidate () operand
          field false
        k) m₀ =
      (do
        let operand ← (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
          (Miri.Interpreter.OperandPath.aggregate 0) (translateOperand op) (some fl)
        (annealAggregateHooksLM2_4 body.localDecls body.layouts).copyOpNoValidate () operand
          ⟨.memory mp, fl⟩ false
        k) m₀ := by
    intro k
    simp only [aggLM2_4_projectDowncast, hunionLay, ↓reduceIte, beq_self_eq_true,
      aggLM2_4_projectField, bind, EStateM.bind, pure, EStateM.pure, hfield]
    rfl
  have hframe₀ : FrameRelLM2_4 body m.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_u hlt_u
  have hop₀ : WellTypedScalarOperand body topFrame₀ op f0Ty := hop_tf.cache_layout hlt_u lay
  have hlm_op_eq : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
      (some fl) = annealEvalOperand body.localDecls body.layouts (translateOperand op) (some fl) := by
    funext st; rw [annealEvalOperandLM2_4_scalar hop₀]
  rcases evalScalarOperand_LM2_4 hframe₀ hprim0 hop₀ s.memory.globals (some fl) with
    ⟨ha_ub, _⟩ | ⟨sc', msc, tf₁, ha_ok', hm_ok, hframe₁, _, _, htf₁, hind₁, hrel', himm'⟩
  · rw [hop_ok] at ha_ub; cases ha_ub
  rw [hop_ok] at ha_ok'; injection ha_ok' with hv _; injection hv with hsc_eq; subst hsc_eq
  obtain ⟨hsz_k, hkv⟩ : (translateTy f0Ty body.layouts).layout.size =
      translateSizeBytes sc.sizeBytes ∧ ValidScalarBytes sc.sizeBytes := by
    cases himm' with | scalar _ _ hr hsz _ _ => exact ⟨hsz, hr.validBytes⟩
  have hk_toNat : (translateTy f0Ty body.layouts).layout.size.bytes.toNat = sc.sizeBytes := by
    rw [hsz_k]; exact translateSizeBytes_toNat_of_valid hkv
  have hk_lt : sc.sizeBytes < sc_old.sizeBytes := by rw [← hk_toNat]; exact hlt_width
  have hk_le_old : sc.sizeBytes ≤ sc_old.sizeBytes := Nat.le_of_lt hk_lt
  have hk_le_S : sc.sizeBytes ≤ S := Nat.le_trans hk_le_old hk_old
  have hS := hwt.size_valid
  have hS16 : S ≤ 16 := by rcases hS with h | h | h | h | h <;> omega
  obtain ⟨M', hset_mask, hM'⟩ := hmask_old.setRange_le hS hrel_old.validBytes hkv hk_le_old hk_old
  obtain ⟨A', hw_alloc, hA'_sz, hA'_len, _, _, _, hA'_mask, _, _, hA'_raw, hA'_high⟩ :=
    union_writeScalar_prefix_preserve_high hrel' hlen_old hsz_old hS16 hk_le_S hmut_old hp_old hset_mask
  obtain ⟨allocIdx, _, hfindIdx, hget_live, hset_live⟩ := array_findIdx?_of_nodup_fst hnodup hlive_old
  obtain ⟨_, hmem_live', _⟩ := hset_live ⟨la_old.kind, A'⟩
  have hoff : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr') = Miri.ABI.Size.ZERO := by
    rw [hptr]; simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
  let mach₃ := inplaceMachine m.machine allocIdx allocId la_old.kind A'
  let st₃ : AnnealStepState := { stack := ⟨#[tf₁]⟩, machine := mach₃ }
  have hw_imm : annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc)) ⟨.memory mp, fl⟩
      { stack := ⟨#[tf₁]⟩, machine := m.machine } = .ok () st₃ := by
    rcases la_old with ⟨kind_old, alloc_old⟩
    unfold annealWriteImmediateLM2_2 annealWriteIndirectImmediate
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      stack_currentFrame?_singleton ⟨#[tf₁]⟩ tf₁ rfl, hprov, Option.bind,
      Miri.Memory.Provenance.getAllocId, hbase, add_size_zero_bytes, hoff, hfindIdx, hget_live,
      show (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).size = msc.size from rfl,
      hw_alloc, pure, EStateM.pure, set, MonadStateOf.set, EStateM.set]
    rfl
  have hev_ok : (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.aggregate 0) (translateOperand op) (some fl) m₀ =
      .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy f0Ty body.layouts⟩
        { stack := ⟨#[tf₁]⟩, machine := m.machine } := by
    show (do let opTy ← annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) (some fl)
             let imm ← annealReadImmediateLM2_2 opTy
             return (⟨.immediate imm.imm, imm.layout⟩ : Miri.Interpreter.OpTy AnnealProv)) m₀ = _
    rw [hlm_op_eq, EStateM.bind_eq_ok hm_ok]; rfl
  have hcopy : (annealAggregateHooksLM2_4 body.localDecls body.layouts).copyOpNoValidate ()
      ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy f0Ty body.layouts⟩
      ⟨.memory mp, fl⟩ false { stack := ⟨#[tf₁]⟩, machine := m.machine } = .ok () st₃ := by
    rw [aggLM2_4_copyOpNoValidate]
    simp only [bind, EStateM.bind, annealReadImmediateLM2_2, pure, EStateM.pure]
    exact hw_imm
  have hu₀ : topFrame₀.locals[u]? = some ⟨.live (.indirect mp), some lay⟩ := by
    dsimp only [topFrame₀, cacheFrameLocalLayout]; rw [Array.getElem?_set_self]; simp [hmls_u_eq]
  have hu₁ : tf₁.locals[u]? = some ⟨.live (.indirect mp), some lay⟩ := by
    rw [hind₁ u mp (some lay) hu₀, hu₀]
  have hlt₁ : u < tf₁.locals.size := by
    rw [hframe₁.mf_locals_size, ← hframe.mf_locals_size]; exact hlt_u
  have hu₁_val : (tf₁.locals[u]'hlt₁).value = .live (.indirect mp) := by
    have h := Array.getElem?_eq_getElem hlt₁
    rw [hu₁] at h; exact congrArg Miri.Interpreter.LocalState.value (Option.some.inj h).symm
  have htf₁_id : tf₁.localsIdentity = topFrame.localsIdentity := by rw [htf₁]; rfl
  have hdisc : (annealAggregateHooksLM2_4 body.localDecls body.layouts).writeDiscriminant () 0
      destPlace st₃ = .ok () st₃ := by
    rw [aggLM2_4_writeDiscriminant]
    have hens : annealEnsureAllocated destPlace st₃ = .ok mp st₃ := by
      dsimp only [destPlace]; rw [← htf₁_id]
      exact annealEnsureAllocated_indirect rfl hlt₁ hu₁_val
    rw [EStateM.bind_eq_ok hens]; rfl
  have hwa : Miri.Interpreter.writeAggregate
      (annealAggregateHooksLM2_4 body.localDecls body.layouts) ()
      (.Adt 0 0 #[] none (some f)) #[translateOperand op] destPlace m₀ = .ok () st₃ := by
    rw [writeAggregate_union_def, hwa_pre, EStateM.bind_eq_ok hev_ok, EStateM.bind_eq_ok hcopy,
      EStateM.bind_eq_ok hdisc]
    rfl
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩) m =
      (st₃, .ok ()) := by
    rw [hm_eval]; unfold Miri.Interpreter.runRvalue; rw [hwa]
  have htf₁_loc : tf₁.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
    rw [htf₁]; exact hframe.location_eq
  have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
    hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl htf₁_loc
  have hrv_spec := evalRvalue_unionAggregate_activeField_eq (locals := s.frame.locals) hbor hcaller
    hdecl_u hadt hwt hfields hf hfl hprim0 hfl_sz hop_tf hdecls_adt
  let locals₂ := s.frame.locals.set u (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))
  have ha_ok : evalStmt s ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩
      body.localDecls body.layouts = MirStepNode.step (advanceStmt s locals₂ s.memory) := by
    have hrv := hrv_spec.2 sc msc hop_ok himm'
    unfold evalStmt; dsimp only; rw [hrv]; simp only []
    rw [hprot, hbor]; dsimp only [invalidateConflictingBorrows]; rw [hmem_same]
    simp [hu_slot, set?_eq_some_set hlt_af_u, locals₂]
  have hread_new : A'.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
        .ok (.fromScalarInt msc) := by
    have hinit_low : A'.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) =
        .ok (.ok ()) := by
      rw [hA'_mask]
      exact hM'.init hS hrel_old.validBytes hkv hk_old hk_le_old
    exact union_readScalar_prefix hrel' hA'_len (hA'_sz.trans hsz_old) hS16 hk_le_S hinit_low hA'_raw
  refine ⟨⟨_, by rw [hstep_a, ha_ok], ?_⟩, _, msc, A', hstep_m, hrel', hmem_live',
    hA'_mask ▸ hM', hread_new, hA'_high⟩
  simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_u]

/-- `annealMemCopyOp` from an `ArraySliceRel` subslice `subMp` (`allocId`) into
an already memory-backed destination array local `d` (`mp_d` at `destId ≠ allocId`,
offset `0`, exact byte size `layD.layout.size`) overwrites `destId`'s allocation
in place (`cnt = 0` via `zero_array_fromBytes_spec`, `0 < cnt` via
`array_copy_alloc_spec`), yielding `ArraySliceRel` at offset `0`. -/
theorem annealMemCopyOp_inplaceArray
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {d : Nat} {dDecl : LocalDecl} {elemKind : RigidTy} {cnt : Nat}
    (hlt : d < tf.locals.size)
    (hwf_d : WellTypedArrayTy body.layouts dDecl.ty elemKind cnt)
    {mp_d : Miri.Interpreter.MemPlace AnnealProv}
    (hval : (tf.locals[d]'hlt).value = .live (.indirect mp_d))
    (hnodup : LiveAllocsNodup m.machine)
    {subMp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId destId : Miri.Memory.AllocId} {tag tag_d : Miri.Memory.BorTag}
    {baseAddr base_d : UInt64} {srcOff : Miri.ABI.Size}
    {la la_d : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    {sub oldElems : List Value}
    (hne : allocId ≠ destId)
    (hprov : subMp.ptr.provenance = some (.concrete allocId tag))
    (hlive : (allocId, la) ∈ m.machine.memory.live.toList)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hsrcOff : Miri.ABI.Size.ofBytes (subMp.ptr.offset.bytes - baseAddr) = srcOff)
    (hslice : ArraySliceRel elemKind cnt body.layouts sub srcOff la.allocation)
    (hprov_d : mp_d.ptr.provenance = some (.concrete destId tag_d))
    (hlive_d : (destId, la_d) ∈ m.machine.memory.live.toList)
    (hbase_d : m.machine.lookupBaseAddr destId = some base_d)
    (hptr_d : mp_d.ptr.offset = Miri.ABI.Size.ofBytes base_d)
    (hsz_d : la_d.allocation.byteSize = (translateTy dDecl.ty body.layouts).layout.size)
    (hal_d : la_d.allocation.align.pow2 ≤ 29)
    (hslice_d_old : ArraySliceRel elemKind cnt body.layouts oldElems Miri.ABI.Size.ZERO la_d.allocation)
    (srcLay : Miri.Interpreter.LocalLayout) (ident : Miri.Interpreter.LocalsIdentity) :
    ∃ (destIdx : Nat) (dest' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      m.machine.memory.live.findIdx? (fun (k, _) => k == destId) = some destIdx ∧
      annealMemCopyOp body.localDecls body.layouts ⟨.indirect subMp, srcLay⟩
          ⟨.local 0 d none ident, translateTy dDecl.ty body.layouts⟩ m =
        .ok () { m with machine := inplaceMachine m.machine destIdx destId la_d.kind dest' } ∧
      dest'.byteSize = (translateTy dDecl.ty body.layouts).layout.size ∧
      dest'.align = la_d.allocation.align ∧
      ArraySliceRel elemKind cnt body.layouts sub Miri.ABI.Size.ZERO dest' ∧
      LiveAllocsNodup (inplaceMachine m.machine destIdx destId la_d.kind dest') ∧
      (destId, ⟨la_d.kind, dest'⟩) ∈
        (inplaceMachine m.machine destIdx destId la_d.kind dest').memory.live.toList ∧
      (∀ a la', a ≠ destId → (a, la') ∈ m.machine.memory.live.toList →
        (a, la') ∈ (inplaceMachine m.machine destIdx destId la_d.kind dest').memory.live.toList) := by
  let layD := translateTy dDecl.ty body.layouts
  have hforce := annealForceUnionAllocation_indirect_eq (body := body) hframes hlt hval ident layD
  have hfind := array_find?_of_nodup_fst hnodup hlive
  obtain ⟨destIdx, _, hfindIdx_d, hget_d, hset_d⟩ := array_findIdx?_of_nodup_fst hnodup hlive_d
  have hdestOff : Miri.ABI.Size.ofBytes (mp_d.ptr.offset.bytes - base_d) = Miri.ABI.Size.ZERO := by
    rw [hptr_d]; simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
  have hbeqf : (allocId == destId) = false := beq_false_of_ne hne
  rcases la_d with ⟨kind_d, alloc_d⟩
  rcases Nat.eq_zero_or_pos cnt with rfl | hpos
  · have hsub_nil : sub = [] := List.eq_nil_of_length_eq_zero hslice.elems_len
    subst hsub_nil
    have hsz0 : layD.layout.size = Miri.ABI.Size.ZERO := by
      dsimp only [layD]; rw [hwf_d.arr_size]; simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
    have hsz_beq : (layD.layout.size.bytes == 0) = true := by rw [hsz0]; rfl
    have hd_bs_beq : (alloc_d.byteSize.bytes == 0) = true := by rw [hsz_d, hsz0]; rfl
    have hgb_src := getBytesUnchecked_at (A := la.allocation) srcOff layD.layout.size
      hslice.alloc_len (by rw [hsz0]; simpa [Miri.ABI.Size.ZERO] using hslice.slice_in_bounds)
    have hgb_dst := getBytesUnchecked_at (A := alloc_d) Miri.ABI.Size.ZERO layD.layout.size
      hslice_d_old.alloc_len (by rw [hsz0, hsz_d, hsz0]; simp [Miri.ABI.Size.ZERO])
    have hmut_bne : (alloc_d.mutability != .Mut) = false := by rw [hslice_d_old.alloc_mut]; rfl
    obtain ⟨zeroAlloc, hfb, hdest_sz, _, hdest_al, _, _, _, _, _, hslice0⟩ :=
      zero_array_fromBytes_spec elemKind body.layouts (align := alloc_d.align) hal_d alloc_d.extra
    obtain ⟨hnodup', hmem', hother⟩ := hset_d ⟨kind_d, zeroAlloc.withExtra alloc_d.extra⟩
    refine ⟨destIdx, zeroAlloc.withExtra alloc_d.extra, hfindIdx_d, ?_, hdest_sz.trans hsz0.symm,
      hdest_al, hslice0, hnodup', hmem', hother⟩
    unfold annealMemCopyOp
    simp only [layD] at hforce hsz_beq hgb_src hgb_dst ⊢
    simp only [bind, EStateM.bind, hforce, get, getThe, MonadStateOf.get, EStateM.get, hprov,
      hprov_d, Option.bind, Miri.Memory.Provenance.getAllocId, hbase, hbase_d, hfind, hfindIdx_d,
      hget_d, hsrcOff, hdestOff, hsz_beq, ↓reduceIte, hgb_src, hgb_dst, hmut_bne,
      Bool.false_eq_true, hd_bs_beq, hfb, set, MonadStateOf.set, EStateM.set]
    rfl
  · have htot_pos : 0 < cnt *
        (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat :=
      Nat.mul_pos hpos hwf_d.elem_size_pos
    have hsz_nz : (layD.layout.size.bytes == 0) = false := by
      cases h0 : (layD.layout.size.bytes == 0) with
      | false => rfl
      | true =>
        have := eq_of_beq h0
        have htn : layD.layout.size.bytes.toNat = 0 := by rw [this]; rfl
        dsimp only [layD] at htn
        rw [hwf_d.arr_size_toNat] at htn; omega
    obtain ⟨dest', hcopy, hsz', _, hal', _, _, _, _, _, hslice'⟩ :=
      array_copy_alloc_spec hslice hpos hwf_d.elem_size_pos
        (dest := alloc_d)
        (by rw [hslice_d_old.alloc_len, hsz_d, hwf_d.arr_size_toNat])
        (by rw [hsz_d]; exact hwf_d.arr_size)
        hslice_d_old.alloc_mut hslice_d_old.alloc_prov
        (by rw [hslice_d_old.alloc_mask]; rfl)
    have hcopy' : Miri.Memory.Allocation.copy la.allocation
        (Miri.Memory.allocRange srcOff layD.layout.size)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) (allocId == destId) true alloc_d =
          .ok () dest' := by
      rw [hbeqf]; dsimp only [layD]; rw [hwf_d.arr_size]; exact hcopy
    obtain ⟨hnodup', hmem', hother⟩ := hset_d ⟨kind_d, dest'⟩
    refine ⟨destIdx, dest', hfindIdx_d, ?_, hsz'.trans hwf_d.arr_size.symm, hal', hslice',
      hnodup', hmem', hother⟩
    unfold annealMemCopyOp
    simp only [layD] at hforce hsz_nz hcopy' ⊢
    simp only [bind, EStateM.bind, hforce, get, getThe, MonadStateOf.get, EStateM.get, hprov,
      hprov_d, Option.bind, Miri.Memory.Provenance.getAllocId, hbase, hbase_d, hfind, hfindIdx_d,
      hget_d, hsrcOff, hdestOff, hsz_nz, Bool.false_eq_true, ↓reduceIte, hcopy',
      set, MonadStateOf.set, EStateM.set]
    rfl

/-- **`step_subslice_assign_overwrite_simulation`** (`LM-2.4` `A2`):
statement-level simulation for `_d = copy/move a[fromIdx..toIdx]` when `_d` is
either:
1. `.dead` (with an initialized `a` and `SubsliceInBounds`): UB in both machines
   (`StepRelLM2_4.ub` — exercising `annealForceUnionAllocation_dead_err`).
2. Already an initialized memory-backed `[elemKind; cnt]` array local at offset
   `0` (`d ≠ arrIdx`): lockstep in-place overwrite (`StateRelLM2_4` +
   `StepPreservesHighWater m 0`). -/
theorem step_subslice_assign_overwrite_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {d arrIdx : Local} {isMove : Bool}
    {fromIdx toIdx : Nat} {fromEnd : Bool} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨d, .nil⟩ (.use (subsliceReadOperand isMove arrIdx fromIdx toIdx fromEnd)),
            span⟩)
    {dDecl arrDecl : LocalDecl} {elemKind : RigidTy} {count : Nat}
    (hdecl_d : get? body.localDecls d = some dDecl)
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf_arr : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hwf_d : WellTypedArrayTy body.layouts dDecl.ty elemKind
      (subsliceEnd count toIdx fromEnd - fromIdx))
    {elems : List Value}
    (hinit_arr : get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)))
    (hin : SubsliceInBounds count fromIdx toIdx fromEnd) :
    let cnt := subsliceEnd count toIdx fromEnd - fromIdx
    (get? s.frame.locals d = some .dead →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ (oldElems : List Value) (mp_d : Miri.Interpreter.MemPlace AnnealProv)
      (destId : Miri.Memory.AllocId) (tag_d : Miri.Memory.BorTag) (base_d : UInt64)
      (la_d : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind),
      d ≠ arrIdx →
      get? s.frame.locals d = some (.init (.aggregate 0 oldElems)) →
      (∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[d]? = some ⟨.live (.indirect mp_d), c⟩) →
      mp_d.ptr.provenance = some (.concrete destId tag_d) →
      (destId, la_d) ∈ m.machine.memory.live.toList →
      m.machine.lookupBaseAddr destId = some base_d →
      mp_d.ptr.offset = Miri.ABI.Size.ofBytes base_d →
      la_d.allocation.byteSize = (translateTy dDecl.ty body.layouts).layout.size →
      la_d.allocation.align.pow2 ≤ 29 →
      MemPlaceRel m.machine dDecl.ty body.layouts (some (.aggregate 0 oldElems)) mp_d →
      ∃ (s' : MachineState) (m' : AnnealStepState),
        stepMirFn body s = .step s' ∧
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals d = some (.init (.aggregate 0 ((elems.drop fromIdx).take cnt))) ∧
        get? s'.frame.locals arrIdx = some (.init (.aggregate 0 elems)) ∧
        MemPlaceRel m'.machine dDecl.ty body.layouts
          (some (.aggregate 0 ((elems.drop fromIdx).take cnt))) mp_d ∧
        LiveAllocsNodup m'.machine ∧
        StepPreservesHighWater m 0 (m', .ok true)) := by
  dsimp only
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  let op := subsliceReadOperand isMove arrIdx fromIdx toIdx fromEnd
  let cnt := subsliceEnd count toIdx fromEnd - fromIdx
  let layD := translateTy dDecl.ty body.layouts
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot; generalize s.memory = mem; intro hbor hprot; cases mem
    dsimp only at hbor hprot; subst hbor hprot; rfl
  have hstep_a : stepMirFn body s =
      evalStmt s ⟨.assign ⟨d, .nil⟩ (.use op), span⟩ body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt, op]
  obtain ⟨slot_d0, mls_d0, hlt_af_d, hlt_d, hslot_d0, hmls_d0, hmls_d_eq, hloc_d0⟩ :=
    hframe.lookup_local hdecl_d
  let topFrame₀ := cacheFrameLocalLayout topFrame d hlt_d layD
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 d none topFrame.localsIdentity, layD⟩
  have hevalPlace : annealEvalPlace body.localDecls body.layouts ⟨d, #[]⟩ m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_d hdecl_d (by rw [hmls_d_eq]; exact hloc_d0.layout_eq)
  have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
      ⟨d, #[]⟩ true m = .ok destPlace m₀ := hevalPlace
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨d, #[]⟩
      (translateRvalue (.use op)) = true := by
    dsimp only [op]; cases isMove <;>
      simp [lm24Assign, lm24Rvalue, lm24Operand, lm24Place, subsliceReadOperand,
        translateRvalue, translateOperand, translatePlace, translateProjectionElem, isSubsliceElem]
  have hm_pre : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨d, .nil⟩ (.use op), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) (some layD) >>=
          fun src => (annealRvalueHooksLM2_4 body.localDecls body.layouts).copyOp () src destPlace)
        m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace']
    dsimp only [translateRvalue]; rfl
  have hframe₀ : FrameRelLM2_4 body m.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_d hlt_d
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ := hdisj.cache_layout hlt_d _
  have hstate₀ : StateRelLM2_4 body s m₀ :=
    StateRelLM2_4.mk topFrame₀ rfl hretCont ⟨retLay, hretPlace⟩ hframe₀ hcal hstack hbor hprot
      hcaller hdisj₀
  have hsim := evalSubsliceOperand_simulation hstate₀ rfl hnodup hdecl_arr hwf_arr isMove
    fromIdx toIdx fromEnd (some layD)
  dsimp only at hsim
  obtain ⟨_, hinit_op⟩ := hsim
  obtain ⟨mp_arr, topFrame₁, _, _, hmls_arr₁, hother₁, htf₁_eq, hstate₁, hin_op, _⟩ :=
    hinit_op elems hinit_arr
  obtain ⟨ha_op_ok, hm_op_ok, allocId, tag, baseAddr, relOffset, localAlloc,
    hprov_arr, hlive_arr, hbase_arr, hptr_arr, hslice_sub⟩ := hin_op hin
  rcases hstate₁ with ⟨tf₁_s, htf₁_s, _, _, hframe₁, _, _, _, _, _, hdisj₁⟩
  have htf₁_s_eq : tf₁_s = topFrame₁ := by simpa using htf₁_s.symm
  subst tf₁_s; clear htf₁_s
  have hlt_d₁ : d < topFrame₁.locals.size := by
    rw [hframe₁.mf_locals_size, ← hframe.mf_locals_size]; exact hlt_d
  let arrLay := translateTy arrDecl.ty body.layouts
  let es := (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size
  let subMp : Miri.Interpreter.MemPlace AnnealProv :=
    { mp_arr with
      ptr := { mp_arr.ptr with
        offset := Miri.ABI.Size.ofBytes
          (mp_arr.ptr.offset.bytes + es.bytes * UInt64.ofNat fromIdx) },
      metadata := .none }
  let srcLay : Miri.Interpreter.LocalLayout :=
    { ty := arrLay.ty,
      layout := { arrLay.layout with
        fields := .Array es (UInt64.ofNat cnt),
        size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt) } }
  let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
  have huse : usesMemCopy ⟨.indirect subMp, srcLay⟩ = true := rfl
  have hm_op_ok' : annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
      (some layD) m₀ = .ok ⟨.indirect subMp, srcLay⟩ m₁ := hm_op_ok
  let sub := (elems.drop fromIdx).take cnt
  have hvld_sub : validateLoadedValue body.layouts body.localDecls op (.aggregate 0 sub) =
      true := by
    have hpt : placeTy body.localDecls body.layouts
        ⟨arrIdx, [.subslice fromIdx toIdx fromEnd]⟩ = some arrDecl.ty := by
      simp [placeTy, hdecl_arr, resolveProjectedTy]
    cases isMove <;>
      simp [op, subsliceReadOperand, validateLoadedValue, operandTy, hpt, hwf_arr.arr_kind]
  have hrv : evalRvalue s.frame.locals (.use op) s.memory body.localDecls body.layouts =
      .ok (.aggregate 0 sub) s.frame.locals s.memory := by
    unfold evalRvalue; dsimp only; rw [hbor, hcaller, ha_op_ok]
    dsimp only
    change (match validateLoadedValue body.layouts body.localDecls op (.aggregate 0 sub) with
      | false => _ | true => _) = _
    rw [hvld_sub]
    cases isMove <;> rfl
  refine ⟨?_, ?_⟩
  · -- (1) Dead destination `_d`.
    intro hd_dead
    have hd_ne_arr : d ≠ arrIdx := by
      intro heq; subst heq; rw [hd_dead] at hinit_arr; cases hinit_arr
    rw [hd_dead] at hslot_d0; injection hslot_d0 with hslot_d0; subst hslot_d0
    have hd_dead_val := hloc_d0.dead_value
    have hmls_d₁ : topFrame₁.locals[d]? = some { mls_d0 with layout := some layD } := by
      rw [hother₁ d hd_ne_arr]
      dsimp only [topFrame₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set_self, hmls_d_eq]
    have hval_d₁ : (topFrame₁.locals[d]'hlt_d₁).value = .dead := by
      have h := Array.getElem?_eq_getElem hlt_d₁
      rw [hmls_d₁] at h
      have h' := (Option.some.inj h).symm
      rw [h']; exact hd_dead_val
    have hforce_dead := annealForceUnionAllocation_dead_err (body := body) (m := m₁) rfl hlt_d₁ hval_d₁
      topFrame.localsIdentity layD
    have hmc_dead : annealMemCopyOp body.localDecls body.layouts ⟨.indirect subMp, srcLay⟩
        destPlace m₁ = .error (.undefinedBehavior "write to dead local") m₁ := by
      unfold annealMemCopyOp; dsimp only
      rw [EStateM.bind_eq_error hforce_dead]
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨d, .nil⟩ (.use op), span⟩) m =
        (m₁, .error (.undefinedBehavior "write to dead local")) := by
      rw [hm_pre]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hm_op_ok']
      simp only [annealRvalueHooksLM2_4, huse, ↓reduceIte]
      rw [hmc_dead]
    have ha_ub : evalStmt s ⟨.assign ⟨d, .nil⟩ (.use op), span⟩ body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only; rw [hrv]; simp [hd_dead]
    rw [hstep_a, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_stmt]
    exact .ub _ _
  · -- (2) Already memory-backed `[elemKind; cnt]` destination `_d` (`d ≠ arrIdx`).
    intro oldElems mp_d destId tag_d base_d la_d hd_ne_arr hd_slot hd_mls hprov_d hlive_d hbase_d
      hptr_d hsz_d hal_d hmp_d_old
    obtain ⟨c_d, hmls_d'⟩ := hd_mls topFrame hframes
    rw [hmls_d'] at hmls_d0; injection hmls_d0 with hmls_d0; subst hmls_d0
    have hmls_d₁ : topFrame₁.locals[d]? = some ⟨.live (.indirect mp_d), some layD⟩ := by
      rw [hother₁ d hd_ne_arr]
      dsimp only [topFrame₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set_self, hmls_d_eq]
    have hval_d₁ : (topFrame₁.locals[d]'hlt_d₁).value = .live (.indirect mp_d) := by
      have h := Array.getElem?_eq_getElem hlt_d₁
      rw [hmls_d₁] at h
      exact congrArg Miri.Interpreter.LocalState.value (Option.some.inj h).symm
    have hne_id : allocId ≠ destId := by
      intro hid; subst hid
      have hd := hdisj₁ arrIdx d mp_arr mp_d (some arrLay) (some layD) (Ne.symm hd_ne_arr)
        hmls_arr₁ hmls_d₁
      rw [hprov_arr, hprov_d] at hd; exact hd rfl
    cases hmp_d_old with
    | mk destId' tag_d' base_d' relOff_d la_d' hprov_d' hmis_d hmeta_d hlive_d' hbase_d' hovf_d
        hptr_d' _ hal_ptr_d _ _ _ _ harr_d_old =>
    have hid_d_eq : destId' = destId := by
      rw [hprov_d] at hprov_d'; injection hprov_d' with hc; cases hc; rfl
    subst destId'
    have htag_d_eq : tag_d' = tag_d := by
      rw [hprov_d] at hprov_d'; injection hprov_d' with hc; cases hc; rfl
    subst tag_d'
    have hbase_d_eq : base_d' = base_d := by
      rw [hbase_d] at hbase_d'; exact (Option.some.inj hbase_d').symm
    subst base_d'
    have hla_d_eq : la_d' = la_d := by
      have h1 := array_find?_of_nodup_fst hnodup hlive_d'
      have h2 := array_find?_of_nodup_fst hnodup hlive_d
      rw [h1] at h2; exact Prod.mk.inj (Option.some.inj h2) |>.2
    subst la_d'
    have hrel0_nat := MemPlaceRel.relOffset_bytes_eq hovf_d hptr_d'
    have hrel0 : relOff_d = Miri.ABI.Size.ZERO := by
      cases relOff_d with | mk b =>
      simp only [Miri.ABI.Size.ZERO]
      congr 1
      apply UInt64.toNat_inj.mp
      rw [hptr_d] at hrel0_nat
      simpa [Miri.ABI.Size.ofBytes] using hrel0_nat
    subst relOff_d
    obtain ⟨_, _, _, hslice_d_old⟩ := harr_d_old elemKind cnt oldElems hwf_d.arr_kind rfl
    have hfrom_le : fromIdx ≤ count := by rcases hin with ⟨_, h1, h2⟩ | ⟨_, h1⟩ <;> omega
    have hcnt32 := hwf_arr.count_lt_two_pow_32
    have htot_arr := hwf_arr.total_bytes_bound
    have hfrom_toNat : (UInt64.ofNat fromIdx).toNat = fromIdx := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : fromIdx < 2 ^ 64))]
    have hprod_lt : fromIdx * es.bytes.toNat < 2 ^ 64 := by
      have hle := Nat.mul_le_mul_right es.bytes.toNat hfrom_le
      dsimp only [es] at hle htot_arr ⊢; omega
    have hmul_eq : es.bytes * UInt64.ofNat fromIdx = UInt64.ofNat (fromIdx * es.bytes.toNat) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mul, hfrom_toNat, Nat.mul_comm,
        Nat.mod_eq_of_lt (by simpa [UInt64.size] using hprod_lt),
        UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hprod_lt)]
    have hsrcOff : Miri.ABI.Size.ofBytes (subMp.ptr.offset.bytes - baseAddr) =
        Miri.ABI.Size.ofBytes (relOffset.bytes + UInt64.ofNat (fromIdx * es.bytes.toNat)) := by
      have hsub_bytes : subMp.ptr.offset.bytes =
          baseAddr + (relOffset.bytes + es.bytes * UInt64.ofNat fromIdx) := by
        dsimp only [subMp]; rw [hptr_arr]; simp [Miri.ABI.Size.ofBytes, UInt64.add_assoc]
      rw [hsub_bytes, uint64_add_sub_cancel_left, hmul_eq]
    obtain ⟨destIdx, dest', _, hmemcopy, hdest_sz, _, hslice_d, hnodup', hlive_d_new, hother_live⟩ :=
      annealMemCopyOp_inplaceArray (body := body) (m := m₁) rfl hlt_d₁ hwf_d hval_d₁ hnodup
        (subMp := subMp) hne_id hprov_arr hlive_arr hbase_arr hsrcOff hslice_sub hprov_d hlive_d
        hbase_d hptr_d hsz_d hal_d hslice_d_old srcLay topFrame.localsIdentity
    let mach₃ := inplaceMachine m.machine destIdx destId la_d.kind dest'
    let st₃ : AnnealStepState := { stack := ⟨#[topFrame₁]⟩, machine := mach₃ }
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨d, .nil⟩ (.use op), span⟩) m = (st₃, .ok ()) := by
      rw [hm_pre]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hm_op_ok']
      simp only [annealRvalueHooksLM2_4, huse, ↓reduceIte]
      rw [hmemcopy]
    have htf₁_loc : topFrame₁.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
      rw [htf₁_eq]; exact hframe.location_eq
    have htf₁_rc : topFrame₁.returnContinuation = topFrame₀.returnContinuation := by rw [htf₁_eq]
    have htf₁_rp : topFrame₁.returnPlace = topFrame₀.returnPlace := by rw [htf₁_eq]
    have htf₁_id : topFrame₁.localsIdentity = topFrame₀.localsIdentity := by rw [htf₁_eq]
    have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
      hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl htf₁_loc
    let locals₂ := s.frame.locals.set d (.init (.aggregate 0 sub))
    have ha_ok : evalStmt s ⟨.assign ⟨d, .nil⟩ (.use op), span⟩ body.localDecls body.layouts =
        MirStepNode.step (advanceStmt s locals₂ s.memory) := by
      unfold evalStmt; dsimp only; rw [hrv]; simp only []
      rw [hprot, hbor]; dsimp only [invalidateConflictingBorrows]; rw [hmem_same]
      simp [hd_slot, set?_eq_some_set hlt_af_d, locals₂]
    have hmp_d_new : MemPlaceRel mach₃ dDecl.ty body.layouts (some (.aggregate 0 sub)) mp_d := by
      refine .mk destId tag_d base_d Miri.ABI.Size.ZERO ⟨la_d.kind, dest'⟩ hprov_d hmis_d hmeta_d
        hlive_d_new hbase_d hovf_d hptr_d' hslice_d.alloc_mut hal_ptr_d
        (by rw [hdest_sz]; simp [Miri.ABI.Size.ZERO])
        (fun h => nomatch h)
        (fun _ _ _ => ?_)
        (fun _ h => nomatch h)
        (fun ek cnt' es' hk hopt => ?_)
      · rw [hslice_d.alloc_mask, hdest_sz]
        have hend_d : (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy dDecl.ty body.layouts).layout.size).endExclusive =
            .ok (translateTy dDecl.ty body.layouts).layout.size := by
          have hlt0 : Miri.ABI.Size.ZERO.bytes.toNat +
              (translateTy dDecl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64 := by
            simp [Miri.ABI.Size.ZERO]; exact UInt64.toNat_lt _
          have h := allocRange_endExclusive_of_lt (off := Miri.ABI.Size.ZERO)
            (sz := (translateTy dDecl.ty body.layouts).layout.size) hlt0
          simpa [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes] using h
        exact Miri.Memory.InitMask.lazy_initialized_query _ _ _ hend_d (UInt64.le_refl _)
      · rw [hwf_d.arr_kind] at hk
        injection hk with hek hcnt'; subst hek hcnt'
        injection hopt with hagg; injection hagg with _ hes'; subst hes'
        exact ⟨hwf_d.arr_fields, hwf_d.arr_size, hwf_d.arr_align, hslice_d⟩
    let tf_fin := { topFrame₁ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
    let m' : AnnealStepState := { st₃ with stack := ⟨#[tf_fin]⟩ }
    have hframe_fin : FrameRelLM2_4 body mach₃ (advanceStmt s locals₂ s.memory).frame tf_fin :=
      { body_eq := hframe₁.body_eq
        location_eq := rfl
        af_locals_len := by
          show (s.frame.locals.set d _).length = _; rw [List.length_set]; exact hframe.af_locals_len
        mf_locals_size := hframe₁.mf_locals_size
        locals_rel := by
          intro i decl slot mls hdecl hslot hmls
          have hslot' : get? locals₂ i = some slot := hslot
          have hmls' : topFrame₁.locals[i]? = some mls := hmls
          rw [get?_eq_getElem?, List.getElem?_set] at hslot'
          by_cases hid : d = i
          · subst hid
            simp only [↓reduceIte, hlt_af_d, Option.some.injEq] at hslot'
            subst hslot'
            rw [hmls_d₁] at hmls'; injection hmls' with hmls'; subst hmls'
            rw [hdecl_d] at hdecl; cases hdecl
            exact .base _ _ (.indirect _ mp_d _
              (fun l hl => (Option.some.inj hl).symm)
              (fun h => nomatch h) hmp_d_new)
          · simp only [hid, ↓reduceIte] at hslot'
            have hloc := hframe₁.locals_rel i decl slot mls hdecl hslot' hmls'
            refine hloc.of_entry ?_
            intro mp_i c_i hmi a la' hpa hla'
            subst hmi
            have hne_a : a ≠ destId := by
              intro hae; subst hae
              have hd := hdisj₁ d i mp_d mp_i (some layD) c_i hid hmls_d₁ hmls'
              rw [hprov_d, hpa] at hd; exact hd rfl
            exact ⟨hother_live a la' hne_a hla', rfl⟩ }
    have hstate' : StateRelLM2_4 body (advanceStmt s locals₂ s.memory) m' :=
      StateRelLM2_4.mk tf_fin rfl
        (by show topFrame₁.returnContinuation = _; rw [htf₁_rc]; exact hretCont)
        ⟨retLay, by show topFrame₁.returnPlace = .frameLocal 0 0 none retLay topFrame₁.localsIdentity
                    rw [htf₁_rp, htf₁_id]; exact hretPlace⟩
        hframe_fin hcal hstack hbor hprot hcaller hdisj₁
    refine ⟨advanceStmt s locals₂ s.memory, m', by rw [hstep_a, ha_ok], hstep_m, hstate',
      ?_, ?_, hmp_d_new, hnodup', ?_⟩
    · simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_d, sub, cnt]
    · simp [advanceStmt, locals₂, get?_eq_getElem?, List.getElem?_set_ne hd_ne_arr]
      rwa [← get?_eq_getElem?]
    · intro _ hw0 _
      obtain ⟨hw', hnext⟩ := MemoryHighWater.inplaceMachine (kind := la_d.kind) (alloc := dest')
        (allocIdx := destIdx) hw0 hlive_d
      exact ⟨hw', by rw [hnext]; omega⟩

/-! ## 17. `Subslice` Composition, Projected `Subslice` Writes, and `Repeat` on Union Fields

`evalProjection_nested_subslice_simulation` composes two `Subslice` projections,
`step_subslice_elem_write_simulation` simulates projected writes whose LHS
destination places chain `.Subslice` with `.ConstantIndex`
(`annealEvalSubslicePlace`), and
`step_repeat_union_field_simulation` exercises `Rvalue.Repeat` on union field
operands (`annealRvalueHooksLM2_4.writeRepeat`). -/

private def fitsI64CopyLM2_4 (value : Int) : Bool :=
  -(2 ^ 63 : Int) ≤ value && value < (2 ^ 63 : Int)

private theorem checkedBounds_def_lm24
    (target : Miri.Memory.PointerArithmetic) (id : Miri.Memory.AllocId)
    (allocationSize offset : Miri.ABI.Size) (signedSize : Int)
    (message : Miri.Memory.CheckInAllocMsg) :
    Miri.Memory.checkedBounds target id allocationSize offset signedSize message =
      (do
        if !fitsI64CopyLM2_4 signedSize then
          throw (.signedSizeOutsideI64 signedSize)
        let offsetNat := offset.bytes.toNat
        let allocationNat := allocationSize.bytes.toNat
        let inBounds := if signedSize >= 0 then
            offsetNat + signedSize.toNat ≤ allocationNat
          else
            let amount := (-signedSize).toNat
            amount ≤ offsetNat && offsetNat ≤ allocationNat
        if !inBounds then
          let signedOffset ←
            (target.signExtendToTargetIsize offset.bytes).mapError
              Miri.Memory.AccessError.pointerArithmetic
          throw (.pointerOutOfBounds id allocationSize signedOffset.toInt signedSize message)
        pure ()) := by
  with_unfolding_all rfl

private theorem checkAndDerefPtr_def_lm24 {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (signedSize : Int) (message : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.LiveAllocationLookup) :
    Miri.Memory.checkAndDerefPtr target ptr signedSize message resolve lookup =
      (do
        if !fitsI64CopyLM2_4 signedSize then
          throw (.signedSizeOutsideI64 signedSize)
        if signedSize == 0 then return none
        let resolved ← match resolve ptr signedSize with
          | .ok resolved => pure resolved
          | .error address => throw (.danglingIntegerPointer address signedSize message)
        let allocation ← match lookup resolved.allocId with
          | .ok allocation => pure allocation
          | .error (.deadAllocation id) => throw (.allocationLookup (.deadAllocation id))
          | .error (.unavailable id) => throw (.allocationLookup (.unavailable id))
        if allocation.kind == .dead then
          throw (.allocationLookup (.deadAllocation resolved.allocId))
        Miri.Memory.checkedBounds target resolved.allocId allocation.size resolved.offset
          signedSize message
        return some ⟨resolved, allocation⟩) := by
  with_unfolding_all rfl

private theorem fitsI64_nat_of_lt_lm24 {n : Nat} (hn : n < 2 ^ 63) :
    (Int64.ofInt (n : Int)).toInt = (n : Int) ∧
    fitsI64CopyLM2_4 (n : Int) = true := by
  have h1 : (-(2 ^ 63 : Int)) ≤ (n : Int) := by omega
  have h2 : (n : Int) < (2 ^ 63 : Int) := by omega
  refine ⟨Int64.toInt_ofInt_of_le h1 h2, ?_⟩
  unfold fitsI64CopyLM2_4
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true h1, decide_eq_true h2⟩

private theorem checkedBounds_inbounds_nat_lm24
    (target : Miri.Memory.PointerArithmetic)
    (allocId : Miri.Memory.AllocId) (allocSize relOffset : Miri.ABI.Size) (n : Nat)
    (hfits : fitsI64CopyLM2_4 (n : Int) = true)
    (hin : relOffset.bytes.toNat + n ≤ allocSize.bytes.toNat) :
    Miri.Memory.checkedBounds target allocId
      allocSize relOffset (n : Int) .inboundsPointerArithmetic = .ok () := by
  rw [checkedBounds_def_lm24]
  have hge0 : ((0 : Int) ≤ (n : Int)) := Int.natCast_nonneg _
  have hin_le : relOffset.bytes.toNat + (n : Int).toNat ≤ allocSize.bytes.toNat := hin
  dsimp only [GE.ge]
  simp only [hfits, hge0, hin_le, ↓reduceIte, decide_true, Bool.not_true,
    Bool.false_eq_true, pure, Except.pure]

private theorem checkAndDerefPtr_ok_zero_lm24 {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (signedSize : Int) (message : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.LiveAllocationLookup)
    (hfits : fitsI64CopyLM2_4 signedSize = true)
    (hz : (signedSize == 0) = true) :
    Miri.Memory.checkAndDerefPtr target ptr signedSize message resolve lookup = .ok none := by
  rw [checkAndDerefPtr_def_lm24]
  simp only [hfits, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hz, pure, Except.pure]

private theorem checkAndDerefPtr_ok_nonzero_lm24 {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (signedSize : Int) (message : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.LiveAllocationLookup)
    (resolved : Miri.Memory.ResolvedPointer ProvExtra)
    (allocation : Miri.Memory.AllocationInfo)
    (hfits : fitsI64CopyLM2_4 signedSize = true)
    (hne0 : (signedSize == 0) = false)
    (hres : resolve ptr signedSize = .ok resolved)
    (hlook : lookup resolved.allocId = .ok allocation)
    (hnot_dead : (allocation.kind == .dead) = false)
    (hbounds :
      Miri.Memory.checkedBounds target resolved.allocId allocation.size resolved.offset
        signedSize message = .ok ()) :
    Miri.Memory.checkAndDerefPtr target ptr signedSize message resolve lookup =
      .ok (some ⟨resolved, allocation⟩) := by
  rw [checkAndDerefPtr_def_lm24]
  simp only [hfits, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hne0, hres, hlook,
    hnot_dead, hbounds, pure, Except.pure, bind, Except.bind]

private theorem checkPtrAccessSigned_eq_of_deref_lm24 {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (size : Int64) (message : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.LiveAllocationLookup)
    {s : Int} {res : Option (Miri.Memory.CheckedPointerAccess ProvExtra)}
    (hs : size.toInt = s)
    (hd : Miri.Memory.checkAndDerefPtr target ptr s message resolve lookup = .ok res) :
    Miri.Memory.checkPtrAccessSigned target ptr size message resolve lookup = .ok () := by
  unfold Miri.Memory.checkPtrAccessSigned
  rw [hs, hd]
  rfl

private theorem checkPtrAccessSigned_inbounds_nat_lm24
    {Prov ProvExtra : Type}
    (ptr : Miri.Memory.Pointer (Option Prov)) (n : Nat)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.LiveAllocationLookup)
    (hn : n < 2 ^ 63)
    (hbody : n ≠ 0 →
      ∃ allocId relOffset extra allocSize align mutability,
        resolve ptr (n : Int) = .ok ⟨allocId, relOffset, extra⟩ ∧
        lookup allocId = .ok ⟨allocSize, align, .liveData, mutability⟩ ∧
        relOffset.bytes.toNat + n ≤ allocSize.bytes.toNat) :
    Miri.Memory.checkPtrAccessSigned annealPointerArithmetic ptr
      (Int64.ofInt (n : Int)) .inboundsPointerArithmetic resolve lookup = .ok () := by
  obtain ⟨hi64_toInt, hfits⟩ := fitsI64_nat_of_lt_lm24 hn
  by_cases hz : n = 0
  · have hz0 : ((n : Int) == 0) = true := beq_iff_eq.mpr (congrArg Nat.cast hz)
    exact checkPtrAccessSigned_eq_of_deref_lm24 _ _ _ _ _ _ hi64_toInt
      (checkAndDerefPtr_ok_zero_lm24 _ _ _ _ _ _ hfits hz0)
  · obtain ⟨allocId, relOffset, extra, allocSize, align, mutability, hres, hlook, hin⟩ :=
      hbody hz
    have hne0 : ((n : Int) == 0) = false :=
      beq_false_of_ne (by intro h; exact hz (Int.ofNat.inj h))
    have hbounds_ok :=
      checkedBounds_inbounds_nat_lm24 annealPointerArithmetic allocId allocSize relOffset n hfits hin
    exact checkPtrAccessSigned_eq_of_deref_lm24 _ _ _ _ _ _ hi64_toInt
      (checkAndDerefPtr_ok_nonzero_lm24 _ _ _ _ _ _ _ _ hfits hne0 hres hlook rfl hbounds_ok)

/-- `Miri.Interpreter.projectionMemoryOffset` in `OffsetMode.inbounds` succeeds
on any `MemPlace` `mp` at relative offset `relOffset` inside live allocation
`allocId` whenever `baseAddr.toNat + relOffset.bytes.toNat < 2 ^ 64`,
`relOffset.bytes.toNat + offset.bytes.toNat ≤ localAlloc.allocation.byteSize.bytes.toNat`,
and `offset.bytes.toNat < 2 ^ 63`. -/
private theorem projectionMemoryOffset_inbounds_of_alloc
    {mach : AnnealMachine} (hnodup : LiveAllocsNodup mach)
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag}
    {baseAddr : UInt64} {relOffset : Miri.ABI.Size}
    {localAlloc : Miri.Memory.LocalAllocation AnnealProv
      (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind}
    {offset : Miri.ABI.Size}
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hlive : (allocId, localAlloc) ∈ mach.memory.live.toList)
    (hbase : mach.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes))
    (hno_ovf : baseAddr.toNat + relOffset.bytes.toNat < 2 ^ 64)
    (hin : relOffset.bytes.toNat + offset.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat)
    (hoff_i64 : offset.bytes.toNat < 2 ^ 63) :
    Miri.Interpreter.projectionMemoryOffset
      annealPointerArithmetic
      (annealPointerResolver mach)
      (annealLiveAllocationLookup mach)
      mp offset .inbounds .none =
      .ok
        { mp with
          ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + offset.bytes) }
          metadata := .none } := by
  have hnot_ge63 : ¬ (offset.bytes.toNat ≥ 2 ^ 63) := Nat.not_le.mpr hoff_i64
  have hi64_toU64 : (Int64.ofInt (offset.bytes.toNat : Int)).toUInt64 = offset.bytes := by
    rw [show (Int64.ofInt (offset.bytes.toNat : Int)).toUInt64 =
        UInt64.ofBitVec (BitVec.ofInt 64 (offset.bytes.toNat : Int)) from rfl,
      BitVec.ofInt_natCast]
    exact UInt64.ofNat_toNat
  have hwrap :
      mp.ptr.wrappingSignedOffset (Int64.ofInt (offset.bytes.toNat : Int)) annealPointerArithmetic =
      .ok { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + offset.bytes) } := by
    dsimp only [Miri.Memory.Pointer.wrappingSignedOffset]
    rw [hi64_toU64]
    have hsz_eq : Miri.ABI.Size.ofBytes offset.bytes = offset := by cases offset; rfl
    rw [hsz_eq, pointer_wrappingOffset_anneal_eq]
  have hcheck :
      Miri.Memory.checkPtrAccessSigned
        annealPointerArithmetic mp.ptr (Int64.ofInt (offset.bytes.toNat : Int))
        .inboundsPointerArithmetic
        (annealPointerResolver mach)
        (annealLiveAllocationLookup mach) = .ok () := by
    apply checkPtrAccessSigned_inbounds_nat_lm24 mp.ptr offset.bytes.toNat _ _ hoff_i64
    intro _
    have hbase_le : baseAddr ≤ mp.ptr.offset.bytes := by
      have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
      have hsz_lt : baseAddr.toNat + relOffset.bytes.toNat < UInt64.size := by
        simpa [UInt64.size] using hno_ovf
      rw [hbytes, UInt64.le_iff_toNat_le, UInt64.toNat_add, Nat.mod_eq_of_lt hsz_lt]
      exact Nat.le_add_right _ _
    have hrel_eq : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = relOffset := by
      have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
      rw [hbytes, uint64_add_sub_cancel_left]
      cases relOffset; rfl
    have hres_ptr :
        annealPointerResolver mach mp.ptr (offset.bytes.toNat : Int) = .ok ⟨allocId, relOffset, ()⟩ := by
      dsimp only [annealPointerResolver]
      rw [hprov]
      simp only [Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hbase_le,
        ↓reduceIte, hrel_eq]
    have hfind := array_find?_of_nodup_fst hnodup hlive
    have hlookup :
        annealLiveAllocationLookup mach allocId =
          .ok ⟨localAlloc.allocation.byteSize, localAlloc.allocation.align,
               .liveData, localAlloc.allocation.mutability⟩ := by
      dsimp only [annealLiveAllocationLookup]
      simp only [hfind]
    exact ⟨allocId, relOffset, (), localAlloc.allocation.byteSize, localAlloc.allocation.align,
      localAlloc.allocation.mutability, hres_ptr, hlookup, hin⟩
  dsimp only [Miri.Interpreter.projectionMemoryOffset, Miri.Interpreter.MemPlace.offsetWithMeta,
    Miri.Interpreter.ptrOffsetInbounds, GE.ge]
  have hmeta_false : (Miri.Interpreter.MemPlaceMeta.none (Prov := AnnealProv)).hasMeta = false := rfl
  simp only [hmeta_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    hnot_ge63, hcheck, hwrap, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- **`evalProjection_nested_subslice_simulation`** (`LM-2.4`): composing two
`Subslice` projections `[.subslice f1 t1 fe1, .subslice f2 t2 fe2]` on a
memory-backed array `a` of `count` primitive scalars related by `MemPlaceRel`.

When the outer subslice `[f1, subsliceEnd count t1 fe1)` is in bounds (yielding
intermediate length `cnt1`):
1. If the inner subslice `(f2, t2, fe2)` is in bounds of `cnt1` (yielding
   length `cnt2`), Anneal extracts `(sub1.drop f2).take cnt2`, and `lean-miri`
   advances to offset `(f1 + f2) * elemSize` with layout `[T; cnt2]`, satisfying
   `ArraySliceRel` at `(f1 + f2) * elemSize` bytes past `relOffset`.
2. If the inner subslice is counted from the end (`fe2 = true`) and
   `cnt1 < f2 + t2 < 2 ^ 64`, both machines report undefined behavior. -/
theorem evalProjection_nested_subslice_simulation
    {mach : AnnealMachine}
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (locals : List LocalSlot)
    {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {elems : List Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup mach)
    (hmp : MemPlaceRel mach arrTy layouts (some (.aggregate 0 elems)) mp)
    (hovf : mp.ptr.offset.bytes.toNat + (translateTy arrTy layouts).layout.size.bytes.toNat < 2 ^ 64)
    {f1 t1 : Nat} {fe1 : Bool}
    (hin1 : SubsliceInBounds count f1 t1 fe1)
    (f2 t2 : Nat) (fe2 : Bool) :
    let cx := annealSubsliceProjectionCx frame layouts mach
    let arrLay := translateTy arrTy layouts
    let es := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
    let cnt1 := subsliceEnd count t1 fe1 - f1
    let sub1 := (elems.drop f1).take cnt1
    let cnt2 := subsliceEnd cnt1 t2 fe2 - f2
    let sub2 := (sub1.drop f2).take cnt2
    (SubsliceInBounds cnt1 f2 t2 fe2 →
      readProjectedValue locals (.aggregate 0 elems)
        [.subslice f1 t1 fe1, .subslice f2 t2 fe2] = .ok (.aggregate 0 sub2) ∧
      annealProjectList cx ⟨.indirect mp, arrLay⟩
        [.Subslice f1 t1 fe1, .Subslice f2 t2 fe2] =
        .ok ⟨.indirect { mp with
                ptr := { mp.ptr with
                  offset := Miri.ABI.Size.ofBytes
                    (mp.ptr.offset.bytes + es.bytes * UInt64.ofNat (f1 + f2)) },
                metadata := .none },
             { ty := arrLay.ty,
               layout := { arrLay.layout with
                 fields := .Array es (UInt64.ofNat cnt2),
                 size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt2) } }⟩ ∧
      ∃ (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (baseAddr : UInt64)
        (relOffset : Miri.ABI.Size)
        (localAlloc : Miri.Memory.LocalAllocation AnnealProv
          (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind),
        mp.ptr.provenance = some (.concrete allocId tag) ∧
        (allocId, localAlloc) ∈ mach.memory.live.toList ∧
        mach.lookupBaseAddr allocId = some baseAddr ∧
        mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes) ∧
        ArraySliceRel elemKind cnt2 layouts sub2
          (Miri.ABI.Size.ofBytes
            (relOffset.bytes + UInt64.ofNat ((f1 + f2) * es.bytes.toNat)))
          localAlloc.allocation) ∧
    (fe2 = true → cnt1 < f2 + t2 → f2 + t2 < 2 ^ 64 →
      readProjectedValue locals (.aggregate 0 elems)
        [.subslice f1 t1 fe1, .subslice f2 t2 fe2] = .ub ∧
      ∃ msg, (annealProjectList cx ⟨.indirect mp, arrLay⟩
        [.Subslice f1 t1 fe1, .Subslice f2 t2 fe2]).mapError annealLiftProjectionError =
          .error (.undefinedBehavior msg)) := by
  intro cx arrLay es cnt1 sub1 cnt2 sub2
  have hsim1 := (evalProjection_subslice_simulation (mach := mach) frame locals hwf hnodup hmp
    f1 t1 fe1).1 hin1
  dsimp only at hsim1
  obtain ⟨hr1, hpl1, allocId, tag, baseAddr, relOffset, localAlloc, hprov, hlive, hbase, hptr,
    hslice1⟩ := hsim1
  cases hmp with
  | mk allocId' tag' baseAddr' relOffset' localAlloc' hprov' _ _ hlive' hbase' hno_ovf0 hptr' _ _
      hin_arr _ _ _ harr =>
  rw [hprov] at hprov'
  injection hprov' with hc_eq; injection hc_eq with ha_eq ht_eq; subst allocId' tag'
  rw [hbase] at hbase'; injection hbase' with hb_eq; subst baseAddr'
  have hla_eq : localAlloc' = localAlloc := by
    have h1 := array_find?_of_nodup_fst hnodup hlive
    have h2 := array_find?_of_nodup_fst hnodup hlive'
    rw [h1] at h2; exact (Prod.mk.inj (Option.some.inj h2)).2.symm
  subst localAlloc'
  have hrel_eq : relOffset' = relOffset := by
    have hb1 : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
    have hb2 : mp.ptr.offset.bytes = baseAddr + relOffset'.bytes := by rw [hptr']; rfl
    have hsub : baseAddr + relOffset.bytes - baseAddr =
        baseAddr + relOffset'.bytes - baseAddr := by rw [← hb1, hb2]
    rw [uint64_add_sub_cancel_left, uint64_add_sub_cancel_left] at hsub
    cases relOffset; cases relOffset'; dsimp only at hsub; subst hsub; rfl
  subst relOffset'
  have hcnt32 := hwf.count_lt_two_pow_32
  have hf1_cnt1_le : f1 + cnt1 ≤ count := by
    dsimp only [cnt1, subsliceEnd]
    rcases hin1 with ⟨rfl, h1, h2⟩ | ⟨rfl, h1⟩ <;> simp <;> omega
  have hcnt1_le : cnt1 ≤ count := by omega
  have hcnt1_toNat : (UInt64.ofNat cnt1).toNat = cnt1 := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : cnt1 < 2 ^ 64))]
  let mp₁ : Miri.Interpreter.MemPlace AnnealProv :=
    { mp with
      ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + es.bytes * UInt64.ofNat f1) }
      metadata := .none }
  let lay₁ : Miri.Interpreter.LocalLayout :=
    { ty := arrLay.ty,
      layout := { arrLay.layout with
        fields := .Array es (UInt64.ofNat cnt1),
        size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt1) } }
  let next₁ : Miri.Interpreter.OpTy AnnealProv := ⟨.indirect mp₁, lay₁⟩
  have hproj1 : Miri.Interpreter.project cx ⟨.indirect mp, arrLay⟩ (.Subslice f1 t1 fe1) =
      .ok next₁ := by
    change annealProjectList cx ⟨.indirect mp, arrLay⟩ [.Subslice f1 t1 fe1] = .ok next₁ at hpl1
    cases hp : Miri.Interpreter.project cx ⟨.indirect mp, arrLay⟩ (.Subslice f1 t1 fe1) <;>
      simp [annealProjectList, hp, bind, Except.bind] at hpl1
    exact congrArg Except.ok hpl1
  have hlen1 : next₁.len cx = .ok (UInt64.ofNat cnt1) := by
    unfold Miri.Interpreter.OpTy.len
    have his : next₁.layout.layout.isSized = true := hwf.arr_isSized
    have hf : next₁.layout.layout.fields = .Array es (UInt64.ofNat cnt1) := rfl
    rw [his, hf]; rfl
  have hlen_sub1 : ((elems.drop f1).take cnt1).length = cnt1 := hslice1.elems_len
  refine ⟨fun hin2 => ?_, fun hfe2 hoob2 hlt64 => ?_⟩
  · have hf2_le : f2 ≤ cnt1 := by rcases hin2 with ⟨_, h1, h2⟩ | ⟨_, h1⟩ <;> omega
    have ht2_le : t2 ≤ cnt1 := by rcases hin2 with ⟨_, _, h2⟩ | ⟨_, h1⟩ <;> omega
    have hf2_cnt2_le : f2 + cnt2 ≤ cnt1 := by
      dsimp only [cnt2, subsliceEnd]
      rcases hin2 with ⟨rfl, h1, h2⟩ | ⟨rfl, h1⟩ <;> simp <;> omega
    have hcnt2_le_count : cnt2 ≤ count := by omega
    have hf2_le_count : f2 ≤ count := by omega
    have hnot_ge64 : ¬(f2 ≥ 2 ^ 64 || t2 ≥ 2 ^ 64) := by
      simp only [GE.ge, Bool.or_eq_true, decide_eq_true_eq, not_or]; omega
    have hf2_toNat : (UInt64.ofNat f2).toNat = f2 := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : f2 < 2 ^ 64))]
    have ht2_toNat : (UInt64.ofNat t2).toNat = t2 := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : t2 < 2 ^ 64))]
    have hcnt2_toNat : (UInt64.ofNat cnt2).toNat = cnt2 := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : cnt2 < 2 ^ 64))]
    have hmul_f2 : es.mul (UInt64.ofNat f2) =
        .ok (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat f2)) :=
      elemSize_mul_ok hwf hf2_le_count
    have hmul_cnt2 : es.mul (UInt64.ofNat cnt2) =
        .ok (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt2)) :=
      elemSize_mul_ok hwf hcnt2_le_count
    have hf1_toNat : (UInt64.ofNat f1).toNat = f1 := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : f1 < 2 ^ 64))]
    have hoff1_toNat : (es.bytes * UInt64.ofNat f1).toNat = f1 * es.bytes.toNat := by
      rw [UInt64.toNat_mul, hf1_toNat, Nat.mul_comm]
      apply Nat.mod_eq_of_lt
      have hle : f1 * es.bytes.toNat ≤ count * es.bytes.toNat := Nat.mul_le_mul_right _ (by omega)
      have htot := hwf.total_bytes_bound
      dsimp only [es] at hle htot ⊢; omega
    have hoff2_toNat : (es.bytes * UInt64.ofNat f2).toNat = f2 * es.bytes.toNat := by
      rw [UInt64.toNat_mul, hf2_toNat, Nat.mul_comm]
      apply Nat.mod_eq_of_lt
      have hle : f2 * es.bytes.toNat ≤ count * es.bytes.toNat := Nat.mul_le_mul_right _ hf2_le_count
      have htot := hwf.total_bytes_bound
      dsimp only [es] at hle htot ⊢; omega
    let rel₁ := Miri.ABI.Size.ofBytes (relOffset.bytes + es.bytes * UInt64.ofNat f1)
    have hptr_mp1 : mp₁.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + rel₁.bytes) := by
      dsimp only [mp₁, rel₁]
      have hb : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
      simp only [Miri.ABI.Size.ofBytes, hb, UInt64.add_assoc]
    have hmp_off_toNat : mp.ptr.offset.bytes.toNat = baseAddr.toNat + relOffset.bytes.toNat := by
      rw [hptr]
      simp only [Miri.ABI.Size.ofBytes, UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by simpa [UInt64.size] using hno_ovf0)
    have hf1_es_le : f1 * es.bytes.toNat ≤ (translateTy arrTy layouts).layout.size.bytes.toNat := by
      rw [hwf.arr_size_toNat]
      exact Nat.mul_le_mul_right _ (by omega)
    have hrel1_toNat : rel₁.bytes.toNat = relOffset.bytes.toNat + f1 * es.bytes.toNat := by
      dsimp only [rel₁]
      simp only [Miri.ABI.Size.ofBytes, UInt64.toNat_add, hoff1_toNat]
      exact Nat.mod_eq_of_lt (by rw [hmp_off_toNat] at hovf; dsimp only [es] at *; omega)
    have hno_ovf1 : baseAddr.toNat + rel₁.bytes.toNat < 2 ^ 64 := by
      rw [hrel1_toNat]
      rw [hmp_off_toNat] at hovf
      dsimp only [es] at *
      omega
    have hin_mp1 : rel₁.bytes.toNat + (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat f2)).bytes.toNat ≤
        localAlloc.allocation.byteSize.bytes.toNat := by
      have h2 : (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat f2)).bytes.toNat =
          f2 * es.bytes.toNat := hoff2_toNat
      rw [hrel1_toNat, h2]
      have hsum_le : (f1 + f2) * es.bytes.toNat ≤
          (translateTy arrTy layouts).layout.size.bytes.toNat := by
        rw [hwf.arr_size_toNat]
        exact Nat.mul_le_mul_right _ (by omega)
      have hdist : f1 * es.bytes.toNat + f2 * es.bytes.toNat = (f1 + f2) * es.bytes.toNat :=
        (Nat.add_mul f1 f2 _).symm
      dsimp only [es] at *
      omega
    have hoff2_i64 : (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat f2)).bytes.toNat < 2 ^ 63 := by
      change (es.bytes * UInt64.ofNat f2).toNat < 2 ^ 63
      rw [hoff2_toNat]
      have hle : f2 * es.bytes.toNat ≤ count * es.bytes.toNat := Nat.mul_le_mul_right _ hf2_le_count
      have htot := hwf.total_bytes_bound
      dsimp only [es] at hle htot ⊢; omega
    have hmo2 := projectionMemoryOffset_inbounds_of_alloc hnodup (mp := mp₁) (relOffset := rel₁)
      (offset := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat f2))
      hprov hlive hbase hptr_mp1 hno_ovf1 hin_mp1 hoff2_i64
    have hsublay2 : cx.subsliceLayout next₁.layout (UInt64.ofNat cnt2) =
        .ok ({ ty := arrLay.ty,
               layout := { arrLay.layout with
                 fields := .Array es (UInt64.ofNat cnt2),
                 size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt2) } }, .none) := by
      show annealSubsliceLayout lay₁ (UInt64.ofNat cnt2) = _
      unfold annealSubsliceLayout
      dsimp only [lay₁]
      simp only [hmul_cnt2]
    have hptr_comb :
        { mp₁ with
          ptr := { mp₁.ptr with
            offset := Miri.ABI.Size.ofBytes (mp₁.ptr.offset.bytes +
              (Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat f2)).bytes) }
          metadata := .none } =
        { mp with
          ptr := { mp.ptr with
            offset := Miri.ABI.Size.ofBytes
              (mp.ptr.offset.bytes + es.bytes * UInt64.ofNat (f1 + f2)) }
          metadata := .none } := by
      dsimp only [mp₁, Miri.ABI.Size.ofBytes]
      congr 1; congr 1; congr 1
      rw [UInt64.add_assoc, UInt64.ofNat_add, UInt64.mul_add]
    have hslice2_raw := hslice1.subslice hf2_cnt2_le
    have hrel_comb :
        Miri.ABI.Size.ofBytes
          ((Miri.ABI.Size.ofBytes (relOffset.bytes + UInt64.ofNat (f1 * es.bytes.toNat))).bytes +
            UInt64.ofNat (f2 * es.bytes.toNat)) =
        Miri.ABI.Size.ofBytes
          (relOffset.bytes + UInt64.ofNat ((f1 + f2) * es.bytes.toNat)) := by
      simp only [Miri.ABI.Size.ofBytes, Nat.add_mul, UInt64.ofNat_add, UInt64.add_assoc]
    dsimp only [es] at hrel_comb
    rw [hrel_comb] at hslice2_raw
    refine ⟨?_, ?_, allocId, tag, baseAddr, relOffset, localAlloc, hprov, hlive, hbase, hptr,
      hslice2_raw⟩
    · have hin2' : SubsliceInBounds (subsliceEnd count t1 fe1 - f1) f2 t2 fe2 := hin2
      have hlen_sub1' : ((elems.drop f1).take (subsliceEnd count t1 fe1 - f1)).length =
          subsliceEnd count t1 fe1 - f1 := hlen_sub1
      simp only [readProjectedValue, extractSubslice_inBounds (elems := elems)
        (by cases harr elemKind count elems hwf.arr_kind rfl with | intro _ h => exact h.2.2.elems_len) hin1,
        extractSubslice_inBounds hlen_sub1' hin2']
      rfl
    · unfold annealProjectList; dsimp only; rw [hproj1]; dsimp only [bind, Except.bind]
      simp only [annealProjectList, bind, Except.bind, Miri.Interpreter.project, hnot_ge64]
      change (do
        let next ← Miri.Interpreter.projectSubslice cx next₁ (UInt64.ofNat f2)
          (UInt64.ofNat t2) fe2
        Except.ok next) = _
      unfold Miri.Interpreter.projectSubslice Miri.Interpreter.prepareSubslice
      have hf1_fields : next₁.layout.layout.fields = .Array es (UInt64.ofNat cnt1) := rfl
      rw [hlen1, hf1_fields]
      rcases hin2 with ⟨rfl, hft2, _⟩ | ⟨rfl, hsum2⟩
      · have hnot_lt2 : ¬(UInt64.ofNat t2 < UInt64.ofNat f2) := by
          simp only [UInt64.lt_iff_toNat_lt, ht2_toNat, hf2_toNat]; omega
        have hcntU2 : UInt64.ofNat t2 - UInt64.ofNat f2 = UInt64.ofNat cnt2 := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_sub_of_le, ht2_toNat, hf2_toNat, hcnt2_toNat]
          · simp [cnt2, subsliceEnd]
          · simp only [UInt64.le_iff_toNat_le, ht2_toNat, hf2_toNat]; omega
        simp only [Bool.false_eq_true, ↓reduceIte, hmul_f2, Except.mapError, hnot_lt2,
          bind, Except.bind, pure, Except.pure, hcntU2, hsublay2]
        unfold Miri.Interpreter.OpTy.offsetWithMeta
        simp only [cx, next₁, annealSubsliceProjectionCx, annealProjectionCx, bind, Except.bind,
          pure, Except.pure]
        rw [hmo2, hptr_comb]
      · have hnot_oob2 : ¬((UInt64.ofNat f2).toNat + (UInt64.ofNat t2).toNat ≥ 2 ^ 64 ||
            (UInt64.ofNat f2).toNat + (UInt64.ofNat t2).toNat > (UInt64.ofNat cnt1).toNat) := by
          rw [hf2_toNat, ht2_toNat, hcnt1_toNat]
          simp only [GE.ge, GT.gt, Bool.or_eq_true, decide_eq_true_eq, not_or]; omega
        have hsub2_toNat : (UInt64.ofNat cnt1 - UInt64.ofNat t2).toNat = cnt1 - t2 := by
          rw [UInt64.toNat_sub_of_le]
          · rw [hcnt1_toNat, ht2_toNat]
          · simp only [UInt64.le_iff_toNat_le, ht2_toNat, hcnt1_toNat, ht2_le]
        have hnot_lt2 : ¬(UInt64.ofNat cnt1 - UInt64.ofNat t2 < UInt64.ofNat f2) := by
          simp only [UInt64.lt_iff_toNat_lt, hsub2_toNat, hf2_toNat]; omega
        have hcntU2 : UInt64.ofNat cnt1 - UInt64.ofNat t2 - UInt64.ofNat f2 =
            UInt64.ofNat cnt2 := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_sub_of_le, hsub2_toNat, hf2_toNat, hcnt2_toNat]
          · simp [cnt2, subsliceEnd]
          · simp only [UInt64.le_iff_toNat_le, hsub2_toNat, hf2_toNat]; omega
        simp only [↓reduceIte, hnot_oob2, Bool.false_eq_true, hmul_f2, Except.mapError, hnot_lt2,
          bind, Except.bind, pure, Except.pure, hcntU2, hsublay2]
        unfold Miri.Interpreter.OpTy.offsetWithMeta
        simp only [cx, next₁, annealSubsliceProjectionCx, annealProjectionCx, bind, Except.bind,
          pure, Except.pure]
        rw [hmo2, hptr_comb]
  · subst hfe2
    have hub : readProjectedValue locals (.aggregate 0 elems)
        [.subslice f1 t1 fe1, .subslice f2 t2 true] = .ub := by
      have hoob2_z : subsliceEnd count t1 fe1 - f1 < f2 + t2 := hoob2
      have hlen_sub1' : ((elems.drop f1).take (subsliceEnd count t1 fe1 - f1)).length =
          subsliceEnd count t1 fe1 - f1 := hlen_sub1
      simp only [readProjectedValue, extractSubslice_inBounds (elems := elems)
        (by cases harr elemKind count elems hwf.arr_kind rfl with | intro _ h => exact h.2.2.elems_len) hin1,
        extractSubslice_fromEnd_oob hlen_sub1' hoob2_z]
    have hnot_ge64 : ¬(f2 ≥ 2 ^ 64 || t2 ≥ 2 ^ 64) := by
      simp only [GE.ge, Bool.or_eq_true, decide_eq_true_eq, not_or]; omega
    have hf2_toNat : (UInt64.ofNat f2).toNat = f2 := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : f2 < 2 ^ 64))]
    have ht2_toNat : (UInt64.ofNat t2).toNat = t2 := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : t2 < 2 ^ 64))]
    have hoob2' : ((UInt64.ofNat f2).toNat + (UInt64.ofNat t2).toNat ≥ 2 ^ 64 ||
        (UInt64.ofNat f2).toNat + (UInt64.ofNat t2).toNat > (UInt64.ofNat cnt1).toNat) = true := by
      rw [hf2_toNat, ht2_toNat, hcnt1_toNat]
      simp only [GE.ge, GT.gt, Bool.or_eq_true, decide_eq_true_eq]; omega
    have hm_oob : ∃ msg, (annealProjectList cx ⟨.indirect mp, arrLay⟩
        [.Subslice f1 t1 fe1, .Subslice f2 t2 true]).mapError annealLiftProjectionError =
          .error (.undefinedBehavior msg) := by
      unfold annealProjectList; dsimp only; rw [hproj1]; dsimp only [bind, Except.bind]
      simp only [annealProjectList, bind, Except.bind, Miri.Interpreter.project, hnot_ge64]
      unfold Miri.Interpreter.projectSubslice Miri.Interpreter.prepareSubslice
      rw [hlen1]
      simp only [↓reduceIte, hoob2', bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
        Except.mapError, annealLiftProjectionError]
      exact ⟨_, rfl⟩
    exact ⟨hub, hm_oob⟩

/-- **`step_subslice_elem_write_simulation`** (`LM-2.4`): projected scalar
assignment `a[fromIdx..toIdx][off of minLen] = const c` (`PlaceElem.Subslice`
followed by `PlaceElem.ConstantIndex` with `fromEnd = false`) on an array local
`a` of `count` primitive scalars on `StateRelLM2_4`.

1. **Dead or uninitialized array (`a = .dead` or `a = .uninit` with
   `0 < count ∨ IsImmediateFrameLocal`)**: both Anneal (`evalStmt`) and
   `lean-miri` (`annealEvalSubslicePlace`) report undefined behavior
   (`StepRelLM2_4.ub`).
2. **Initialized array (`a = .init (.aggregate 0 elems)`) with in-bounds
   subslice (`SubsliceInBounds count fromIdx toIdx fromEnd`, length `cnt`) and
   in-bounds element (`off < minLen ≤ cnt`)**: both Anneal
   (`writeProjectedForLocal` / `replaceSubslice`) and `lean-miri`
   (`annealEvalSubslicePlace` + `annealWriteImmediateLM2_2`) step in lockstep
   (`StateRelLM2_4` / `StepRelLM2_4.step`), updating element `fromIdx + off` in
   place to `.scalar sc` (`MemPlaceRel` for `elems.set (fromIdx + off) (.scalar sc)`,
   `LiveAllocsNodup`, and `StepPreservesHighWater m 0`). -/
theorem step_subslice_elem_write_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {arrIdx : Local} {fromIdx toIdx off minLen : Nat} {fromEnd : Bool}
    {c : ConstOperand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨arrIdx, [.subslice fromIdx toIdx fromEnd, .constantIndex off minLen false]⟩
        (.use (.constant c)), span⟩)
    {arrDecl : LocalDecl} {elemKind : RigidTy} {count : Nat}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    {sc : MirAst.ScalarInt}
    (hcty : c.ty = { kind := elemKind, layoutIdx := 0 })
    (hval : c.val = .scalar (.int sc))
    (hsz_c : ValidScalarBytes sc.sizeBytes)
    (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (helemsz : (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size =
      translateSizeBytes sc.sizeBytes)
    (hbool : elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) :
    let cnt := subsliceEnd count toIdx fromEnd - fromIdx
    ((get? s.frame.locals arrIdx = some .dead ∨
        (get? s.frame.locals arrIdx = some .uninit ∧
          (0 < count ∨ ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf arrIdx))) →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)) →
      SubsliceInBounds count fromIdx toIdx fromEnd →
      off < minLen → minLen ≤ cnt →
      (∀ mp, (∃ tf c_l, m.stack.frames = #[tf] ∧ tf.locals[arrIdx]? = some ⟨.live (.indirect mp), c_l⟩) →
        mp.ptr.offset.bytes.toNat + (translateTy arrDecl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64) →
      ∃ (s' : MachineState) (m' : AnnealStepState) (mp : Miri.Interpreter.MemPlace AnnealProv),
        stepMirFn body s = .step s' ∧
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals arrIdx =
          some (.init (.aggregate 0 (elems.set (fromIdx + off) (.scalar sc)))) ∧
        MemPlaceRel m'.machine arrDecl.ty body.layouts
          (some (.aggregate 0 (elems.set (fromIdx + off) (.scalar sc)))) mp ∧
        LiveAllocsNodup m'.machine ∧
        StepPreservesHighWater m 0 (m', .ok true)) := by
  intro cnt
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot; generalize s.memory = mem; intro hbor hprot; cases mem
    dsimp only at hbor hprot; subst hbor hprot; rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨arrIdx, [.subslice fromIdx toIdx fromEnd, .constantIndex off minLen false]⟩
        (.use (.constant c)), span⟩ body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
  have ha_rv : evalRvalue s.frame.locals (.use (.constant c)) s.memory body.localDecls body.layouts =
      .ok (.scalar sc) s.frame.locals s.memory := by
    have hev : evalOperand s.frame.locals (.constant c) .nil s.memory.globals body.layouts .nil
        body.localDecls = .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    unfold evalRvalue
    dsimp only
    rw [hbor, hcaller]
    simp [hev]
  obtain ⟨slot_arr, mls_arr, hlt_af_arr, hlt_arr, hslot_arr, hmls_arr, hmls_arr_eq, hloc_arr⟩ :=
    hframe.lookup_local hdecl_arr
  let arrLay := translateTy arrDecl.ty body.layouts
  let topFrame' := cacheFrameLocalLayout topFrame arrIdx hlt_arr arrLay
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame']⟩ }
  have hcache_arr : ∀ l, (topFrame.locals[arrIdx]'hlt_arr).layout = some l → l = arrLay := by
    rw [hmls_arr_eq]; exact hloc_arr.layout_eq
  have hres_arr : annealResolveAndCacheLocalLayout body.localDecls body.layouts arrIdx none m =
      .ok (topFrame', arrLay) m₀ :=
    annealResolveAndCacheLocalLayout_eq (known := none) hframes hlt_arr hdecl_arr hcache_arr
  have hlt_arr' : arrIdx < topFrame'.locals.size := by
    unfold topFrame' cacheFrameLocalLayout; simp [hlt_arr]
  have hval_arr' : (topFrame'.locals[arrIdx]'hlt_arr').value = mls_arr.value := by
    unfold topFrame' cacheFrameLocalLayout
    simp [hmls_arr_eq]
  have hnot_empty : m.stack.currentFrame?.isNone = false := by
    rw [stack_currentFrame?_singleton m.stack topFrame hframes]; rfl
  let mirPlace : Miri.MIR.Place :=
    translatePlace ⟨arrIdx, [.subslice fromIdx toIdx fromEnd, .constantIndex off minLen false]⟩
  have hlm24 : lm24Assign body.localDecls body.layouts mirPlace
      (translateRvalue (.use (.constant c))) = true := by
    simp [lm24Assign, lm24Place, mirPlace, translatePlace, translateProjectionElem, isSubsliceElem]
  refine ⟨?_, ?_⟩
  · rintro (hdead | ⟨huninit, hcnt⟩)
    · rw [hdead] at hslot_arr; injection hslot_arr with hse; subst hse
      have ha_ub : evalStmt s
          ⟨.assign ⟨arrIdx, [.subslice fromIdx toIdx fromEnd, .constantIndex off minLen false]⟩
            (.use (.constant c)), span⟩ body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only; rw [ha_rv]; dsimp only; rw [hdead]
      have hdead_v := hloc_arr.dead_value
      have hgop : topFrame'.getLocalOperand arrIdx = .error (.localExpectedLive arrIdx) := by
        unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
          Miri.Interpreter.LocalState.access
        simp [hlt_arr', hval_arr', hdead_v, bind, Except.bind, pure, Except.pure, Except.mapError]
      have hp_err : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
          mirPlace true m = .error (.undefinedBehavior "projected write to dead local") m₀ := by
        show annealEvalSubslicePlace body.localDecls body.layouts mirPlace m = _
        unfold annealEvalSubslicePlace
        simp [mirPlace, translatePlace, get, getThe, MonadStateOf.get, EStateM.get, bind,
          EStateM.bind, hnot_empty, hres_arr, hgop, throw, throwThe, MonadExceptOf.throw,
          EStateM.throw]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_4 body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨arrIdx, [.subslice fromIdx toIdx fromEnd,
            .constantIndex off minLen false]⟩ (.use (.constant c)), span⟩) m =
          (m₀, .error (.undefinedBehavior "projected write to dead local")) := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt
        dsimp only [translateStmtKind]
        change (if lm24Assign body.localDecls body.layouts mirPlace
            (translateRvalue (.use (.constant c))) then _ else _) = _
        simp only [hlm24, ↓reduceIte]
        unfold Miri.Interpreter.runRvalue Miri.Interpreter.evalRvalueIntoPlace
        rw [EStateM.bind_eq_error hp_err]
      rw [hstep_a, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
        hbb hstmt hm_err]
      exact .ub _ _
    · rw [huninit] at hslot_arr; injection hslot_arr with hse; subst hse
      have ha_ub : evalStmt s
          ⟨.assign ⟨arrIdx, [.subslice fromIdx toIdx fromEnd, .constantIndex off minLen false]⟩
            (.use (.constant c)), span⟩ body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only; rw [ha_rv]; dsimp only; rw [huninit]; rfl
      cases hloc_arr with
      | base _ _ hl =>
        cases hl with
        | immediate _ imm _ _ hv =>
          rcases hv with ⟨_, rfl⟩ | ⟨_, hv', _⟩
          · have hgop : topFrame'.getLocalOperand arrIdx = .ok (.immediate .uninit) := by
              unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
                Miri.Interpreter.LocalState.access
              simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
            have hp_err : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
                mirPlace true m =
                .error (.undefinedBehavior "projected write to uninitialized local") m₀ := by
              show annealEvalSubslicePlace body.localDecls body.layouts mirPlace m = _
              unfold annealEvalSubslicePlace
              simp [mirPlace, translatePlace, get, getThe, MonadStateOf.get, EStateM.get, bind,
                EStateM.bind, pure, hnot_empty, hres_arr, hgop, throw, throwThe,
                MonadExceptOf.throw, EStateM.throw]
            have hm_err : Miri.Interpreter.Step.evalStatement
                (annealStepHooksLM2_4 body.localDecls body.layouts) ()
                (translateStmt ⟨.assign ⟨arrIdx, [.subslice fromIdx toIdx fromEnd,
                  .constantIndex off minLen false]⟩ (.use (.constant c)), span⟩) m =
                (m₀, .error (.undefinedBehavior "projected write to uninitialized local")) := by
              unfold Miri.Interpreter.Step.evalStatement translateStmt
              dsimp only [translateStmtKind]
              change (if lm24Assign body.localDecls body.layouts mirPlace
                  (translateRvalue (.use (.constant c))) then _ else _) = _
              simp only [hlm24, ↓reduceIte]
              unfold Miri.Interpreter.runRvalue Miri.Interpreter.evalRvalueIntoPlace
              rw [EStateM.bind_eq_error hp_err]
            rw [hstep_a, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq
              hframe.location_eq hbb hstmt hm_err]
            exact .ub _ _
          · cases hv'
        | indirect _ mp _ _ _ hmp =>
          have hgop : topFrame'.getLocalOperand arrIdx = .ok (.indirect mp) := by
            unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
              Miri.Interpreter.LocalState.access
            simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
          have hpos : 0 < count := by
            rcases hcnt with hpos | himm_loc
            · exact hpos
            · exact absurd rfl (himm_loc topFrame hframes _ hmls_arr mp)
          have hchk_err := annealCheckIndirectInitialized_uninit_array_ub hwf hnodup hmp hpos
          have hp_err : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
              mirPlace true m =
              .error (.undefinedBehavior "access to uninitialized indirect place") m₀ := by
            show annealEvalSubslicePlace body.localDecls body.layouts mirPlace m = _
            unfold annealEvalSubslicePlace
            simp [m₀, arrLay, mirPlace, translatePlace, get, getThe, MonadStateOf.get, EStateM.get,
              bind, EStateM.bind, pure, hnot_empty, hres_arr, hgop, hchk_err, throw,
              throwThe, MonadExceptOf.throw, EStateM.throw]
          have hm_err : Miri.Interpreter.Step.evalStatement
              (annealStepHooksLM2_4 body.localDecls body.layouts) ()
              (translateStmt ⟨.assign ⟨arrIdx, [.subslice fromIdx toIdx fromEnd,
                .constantIndex off minLen false]⟩ (.use (.constant c)), span⟩) m =
              (m₀, .error (.undefinedBehavior "access to uninitialized indirect place")) := by
            unfold Miri.Interpreter.Step.evalStatement translateStmt
            dsimp only [translateStmtKind]
            change (if lm24Assign body.localDecls body.layouts mirPlace
                (translateRvalue (.use (.constant c))) then _ else _) = _
            simp only [hlm24, ↓reduceIte]
            unfold Miri.Interpreter.runRvalue Miri.Interpreter.evalRvalueIntoPlace
            rw [EStateM.bind_eq_error hp_err]
          rw [hstep_a, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq
            hframe.location_eq hbb hstmt hm_err]
          exact .ub _ _
  · intro elems hinit hin hoff_lt hmin_le hovf_fn
    rw [hinit] at hslot_arr; injection hslot_arr with hse; subst hse
    cases hloc_arr with
    | union _ _ _ _ _ _ _ _ hwt _ _ _ =>
      obtain ⟨n, hn, _⟩ := hwt.fields_union
      rw [hwf.arr_fields] at hn; cases hn
    | base _ _ hl =>
      obtain ⟨mp, cachedLay, rfl, _, hmp⟩ := hl.array_init_is_indirect hwf.arr_kind
      have hovf := hovf_fn mp ⟨topFrame, cachedLay, hframes, hmls_arr⟩
      have hgop : topFrame'.getLocalOperand arrIdx = .ok (.indirect mp) := by
        unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
          Miri.Interpreter.LocalState.access
        simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
      have hchk_ok : annealCheckIndirectInitialized m.machine mp arrLay.layout.size = .ok () :=
        annealCheckIndirectInitialized_of_array_memPlaceRel hwf hnodup hmp
      let cx := annealSubsliceProjectionCx topFrame' body.layouts m.machine
      let elemTy : Ty := { kind := elemKind, layoutIdx := 0 }
      let elemLay := translateTy elemTy body.layouts
      let es := elemLay.layout.size
      have hsim1 := (evalProjection_subslice_simulation (mach := m.machine) topFrame'
        s.frame.locals hwf hnodup hmp fromIdx toIdx fromEnd).1 hin
      dsimp only at hsim1
      obtain ⟨_, hpl1, allocId, tag, baseAddr, relOffset, localAlloc, hprov, hlive, hbase, hptr,
        _⟩ := hsim1
      cases hmp with
      | mk allocId' tag' baseAddr' relOffset' localAlloc' hprov' hmis hmeta hlive' hbase' hno_ovf0
          hptr' hmut haligned hin_arr _ hval_cons _ harr =>
      rw [hprov] at hprov'
      injection hprov' with hc_eq; injection hc_eq with ha_eq ht_eq; subst allocId' tag'
      rw [hbase] at hbase'; injection hbase' with hb_eq; subst baseAddr'
      have hla_eq : localAlloc' = localAlloc := by
        have h1 := array_find?_of_nodup_fst hnodup hlive
        have h2 := array_find?_of_nodup_fst hnodup hlive'
        rw [h1] at h2; exact (Prod.mk.inj (Option.some.inj h2)).2.symm
      subst localAlloc'
      have hrel_eq : relOffset' = relOffset := by
        have hb1 : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
        have hb2 : mp.ptr.offset.bytes = baseAddr + relOffset'.bytes := by rw [hptr']; rfl
        have hsub : baseAddr + relOffset.bytes - baseAddr =
            baseAddr + relOffset'.bytes - baseAddr := by rw [← hb1, hb2]
        rw [uint64_add_sub_cancel_left, uint64_add_sub_cancel_left] at hsub
        cases relOffset; cases relOffset'; dsimp only at hsub; subst hsub; rfl
      subst relOffset'
      obtain ⟨_, _, _, hslice⟩ := harr elemKind count elems hwf.arr_kind rfl
      have hcnt32 := hwf.count_lt_two_pow_32
      have hfrom_cnt_le : fromIdx + cnt ≤ count := by
        dsimp only [cnt, subsliceEnd]
        rcases hin with ⟨rfl, h1, h2⟩ | ⟨rfl, h1⟩ <;> simp <;> omega
      have hidx_lt : fromIdx + off < count := by omega
      let mp₁ : Miri.Interpreter.MemPlace AnnealProv :=
        { mp with
          ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + es.bytes * UInt64.ofNat fromIdx) }
          metadata := .none }
      let lay₁ : Miri.Interpreter.LocalLayout :=
        { ty := arrLay.ty,
          layout := { arrLay.layout with
            fields := .Array es (UInt64.ofNat cnt),
            size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt) } }
      let next₁ : Miri.Interpreter.OpTy AnnealProv := ⟨.indirect mp₁, lay₁⟩
      have hproj1 : Miri.Interpreter.project cx ⟨.indirect mp, arrLay⟩
          (.Subslice fromIdx toIdx fromEnd) = .ok next₁ := by
        change annealProjectList cx ⟨.indirect mp, arrLay⟩ [.Subslice fromIdx toIdx fromEnd] =
          .ok next₁ at hpl1
        cases hp : Miri.Interpreter.project cx ⟨.indirect mp, arrLay⟩ (.Subslice fromIdx toIdx fromEnd) <;>
          simp [annealProjectList, hp, bind, Except.bind] at hpl1
        exact congrArg Except.ok hpl1
      have hlen1 : next₁.len cx = .ok (UInt64.ofNat cnt) := by
        unfold Miri.Interpreter.OpTy.len
        have his : next₁.layout.layout.isSized = true := hwf.arr_isSized
        have hf : next₁.layout.layout.fields = .Array es (UInt64.ofNat cnt) := rfl
        rw [his, hf]; rfl
      have hoff_toNat : (UInt64.ofNat off).toNat = off := by
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : off < 2 ^ 64))]
      have hmin_toNat : (UInt64.ofNat minLen).toNat = minLen := by
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : minLen < 2 ^ 64))]
      have hcnt_toNat : (UInt64.ofNat cnt).toNat = cnt := by
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : cnt < 2 ^ 64))]
      have hnot_ovf_ci : ¬ (off ≥ 2 ^ 64 || minLen ≥ 2 ^ 64) := by
        simp only [GE.ge, Bool.or_eq_true, decide_eq_true_eq, not_or]; omega
      have hnot_lt_min : ¬ (UInt64.ofNat cnt < UInt64.ofNat minLen) := by
        simp only [UInt64.lt_iff_toNat_lt, hcnt_toNat, hmin_toNat]; omega
      have hnot_ge_min : ¬ (UInt64.ofNat off ≥ UInt64.ofNat minLen) := by
        simp only [GE.ge, UInt64.le_iff_toNat_le, hoff_toNat, hmin_toNat]; omega
      have hnot_ge_cnt : ¬ (UInt64.ofNat off ≥ UInt64.ofNat cnt) := by
        simp only [GE.ge, UInt64.le_iff_toNat_le, hoff_toNat, hcnt_toNat]; omega
      have hcomp : Miri.Interpreter.IntegerOps.computeSizeInBytes
          es (UInt64.ofNat off) cx.maxSizeOfVal =
          some (Miri.ABI.Size.ofBytes (UInt64.ofNat (off * es.bytes.toNat))) := by
        unfold Miri.Interpreter.IntegerOps.computeSizeInBytes
        rw [hoff_toNat, Nat.mul_comm]
        have h1 : off * es.bytes.toNat ≤ count * es.bytes.toNat := Nat.mul_le_mul_right _ (by omega)
        have h2 := hwf.total_bytes_bound
        dsimp only [es, elemLay, elemTy] at h1 ⊢
        have hc1 : off * (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat <
            2 ^ 64 := by omega
        have hc2 : off * (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat ≤
            cx.maxSizeOfVal.bytes.toNat := by
          have hmax : cx.maxSizeOfVal.bytes.toNat = 0x7fff_ffff_ffff_ffff := rfl
          rw [hmax]; omega
        simp [hc1, hc2]
      have hfield_elem : cx.field next₁.layout 0 = .ok elemLay := by
        dsimp only [cx, next₁, lay₁, annealSubsliceProjectionCx, annealProjectionCx,
          arrayElemLayoutOf, arrLay]
        exact congrArg Except.ok hwf.elem_layout_eq
      have hfrom_toNat : (UInt64.ofNat fromIdx).toNat = fromIdx := by
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : fromIdx < 2 ^ 64))]
      have hoff1_toNat : (es.bytes * UInt64.ofNat fromIdx).toNat = fromIdx * es.bytes.toNat := by
        rw [UInt64.toNat_mul, hfrom_toNat, Nat.mul_comm]
        apply Nat.mod_eq_of_lt
        have hle : fromIdx * es.bytes.toNat ≤ count * es.bytes.toNat := Nat.mul_le_mul_right _ (by omega)
        have htot := hwf.total_bytes_bound
        dsimp only [es, elemLay, elemTy] at hle htot ⊢; omega
      let rel₁ := Miri.ABI.Size.ofBytes (relOffset.bytes + es.bytes * UInt64.ofNat fromIdx)
      let offSz := Miri.ABI.Size.ofBytes (UInt64.ofNat (off * es.bytes.toNat))
      have hptr_mp1 : mp₁.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + rel₁.bytes) := by
        dsimp only [mp₁, rel₁]
        have hb : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
        simp only [Miri.ABI.Size.ofBytes, hb, UInt64.add_assoc]
      have hmp_off_toNat : mp.ptr.offset.bytes.toNat = baseAddr.toNat + relOffset.bytes.toNat := by
        rw [hptr]
        simp only [Miri.ABI.Size.ofBytes, UInt64.toNat_add]
        exact Nat.mod_eq_of_lt (by simpa [UInt64.size] using hno_ovf0)
      have hrel1_toNat : rel₁.bytes.toNat = relOffset.bytes.toNat + fromIdx * es.bytes.toNat := by
        dsimp only [rel₁]
        simp only [Miri.ABI.Size.ofBytes, UInt64.toNat_add, hoff1_toNat]
        have hle : fromIdx * es.bytes.toNat ≤ (translateTy arrDecl.ty body.layouts).layout.size.bytes.toNat := by
          rw [hwf.arr_size_toNat]; exact Nat.mul_le_mul_right _ (by omega)
        exact Nat.mod_eq_of_lt (by rw [hmp_off_toNat] at hovf; dsimp only [es, elemLay, elemTy] at *; omega)
      have hoffSz_toNat : offSz.bytes.toNat = off * es.bytes.toNat := by
        dsimp only [offSz, Miri.ABI.Size.ofBytes]
        have hle : off * es.bytes.toNat ≤ count * es.bytes.toNat := Nat.mul_le_mul_right _ (by omega)
        have htot := hwf.total_bytes_bound
        dsimp only [es, elemLay, elemTy] at hle htot ⊢
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : off * _ < 2 ^ 64))]
      have hno_ovf1 : baseAddr.toNat + rel₁.bytes.toNat < 2 ^ 64 := by
        rw [hrel1_toNat]; rw [hmp_off_toNat] at hovf
        have hle : fromIdx * es.bytes.toNat ≤ (translateTy arrDecl.ty body.layouts).layout.size.bytes.toNat := by
          rw [hwf.arr_size_toNat]; exact Nat.mul_le_mul_right _ (by omega)
        dsimp only [es, elemLay, elemTy] at *; omega
      have hin_mp1 : rel₁.bytes.toNat + offSz.bytes.toNat ≤ localAlloc.allocation.byteSize.bytes.toNat := by
        rw [hrel1_toNat, hoffSz_toNat]
        have hsum_le : (fromIdx + off) * es.bytes.toNat ≤
            (translateTy arrDecl.ty body.layouts).layout.size.bytes.toNat := by
          rw [hwf.arr_size_toNat]; exact Nat.mul_le_mul_right _ (by omega)
        have hdist : fromIdx * es.bytes.toNat + off * es.bytes.toNat = (fromIdx + off) * es.bytes.toNat :=
          (Nat.add_mul fromIdx off _).symm
        dsimp only [es, elemLay, elemTy] at *; omega
      have hoffSz_i64 : offSz.bytes.toNat < 2 ^ 63 := by
        rw [hoffSz_toNat]
        have hle : off * es.bytes.toNat ≤ count * es.bytes.toNat := Nat.mul_le_mul_right _ (by omega)
        have htot := hwf.total_bytes_bound
        dsimp only [es, elemLay, elemTy] at hle htot ⊢; omega
      have hmo_elem := projectionMemoryOffset_inbounds_of_alloc hnodup (mp := mp₁) (relOffset := rel₁)
        (offset := offSz) hprov hlive hbase hptr_mp1 hno_ovf1 hin_mp1 hoffSz_i64
      let elemMp : Miri.Interpreter.MemPlace AnnealProv :=
        { mp with
          ptr := { mp.ptr with
            offset := Miri.ABI.Size.ofBytes
              (mp.ptr.offset.bytes + UInt64.ofNat ((fromIdx + off) * es.bytes.toNat)) }
          metadata := .none }
      have helemMp_eq :
          { mp₁ with
            ptr := { mp₁.ptr with offset := Miri.ABI.Size.ofBytes (mp₁.ptr.offset.bytes + offSz.bytes) }
            metadata := .none } = elemMp := by
        dsimp only [mp₁, elemMp, offSz, Miri.ABI.Size.ofBytes]
        congr 1; congr 1; congr 1
        have hmul_eq : es.bytes * UInt64.ofNat fromIdx = UInt64.ofNat (fromIdx * es.bytes.toNat) := by
          apply UInt64.toNat_inj.mp
          rw [hoff1_toNat, UInt64.toNat_ofNat',
            Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by rw [← hoff1_toNat]; exact UInt64.toNat_lt _))]
        rw [UInt64.add_assoc, hmul_eq, ← UInt64.ofNat_add, ← Nat.add_mul]
      have hpl_both : annealProjectList cx ⟨.indirect mp, arrLay⟩
          [.Subslice fromIdx toIdx fromEnd, .ConstantIndex off minLen false] =
          .ok ⟨.indirect elemMp, elemLay⟩ := by
        unfold annealProjectList; dsimp only; rw [hproj1]; dsimp only [bind, Except.bind]
        simp only [annealProjectList, bind, Except.bind, Miri.Interpreter.project,
          hnot_ovf_ci, ↓reduceIte, Miri.Interpreter.projectConstantIndex, hlen1, hnot_lt_min,
          Bool.false_eq_true, hnot_ge_min, pure, Except.pure]
        unfold Miri.Interpreter.projectIndex
        have hf1_fields : next₁.layout.layout.fields = .Array es (UInt64.ofNat cnt) := rfl
        rw [hf1_fields, hlen1]
        simp only [bind, Except.bind, hnot_ge_cnt, ↓reduceIte, hcomp, hfield_elem]
        unfold Miri.Interpreter.OpTy.offset Miri.Interpreter.OpTy.offsetWithMeta
        have he_sized : elemLay.layout.isSized = true := hwf.elem_isSized
        rw [he_sized]
        dsimp only [cx, next₁, annealSubsliceProjectionCx, annealProjectionCx, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
        rw [hmo_elem, helemMp_eq]
        rfl
      have hplace_ok : annealEvalSubslicePlace body.localDecls body.layouts mirPlace m =
          .ok ⟨.memory elemMp, elemLay⟩ m₀ := by
        unfold annealEvalSubslicePlace
        simp [m₀, mirPlace, translatePlace, translateProjectionElem, arrLay, cx, get, getThe,
          MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure, hnot_empty,
          hres_arr, hgop, hchk_ok, hpl_both]
      obtain ⟨msc, htryU, hrel_sc⟩ := tryFromUInt_of_valid_canonical hsz_c hcan
      have hprim_e : IsPrimScalarTy elemTy := hwf.elem_prim
      have hprim_c : IsPrimScalarTy c.ty := hcty ▸ hprim_e
      have hop_m : annealEvalOperandLM2_4 body.localDecls body.layouts
          (translateOperand (.constant c)) (some elemLay) m₀ =
          .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ m₀ := by
        show annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
          (some elemLay) m₀ = _
        with_unfolding_all
          unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
          dsimp only
          rw [hval]
          simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
            EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
            stack_currentFrame?_singleton m₀.stack topFrame' rfl, Option.isNone_some,
            Bool.false_eq_true, ↓reduceIte, htryU, hprim_c.layoutOfEncoded]
      obtain ⟨alloc', hwrite, hbyteSize, _, hmask', hslice'⟩ :=
        hslice.writeScalar_set hidx_lt hrel_sc helemsz hbool hchar
      obtain ⟨allocIdx, _, hfindIdx, hgetIdx, hset_prop⟩ :=
        array_findIdx?_of_nodup_fst hnodup hlive
      rcases localAlloc with ⟨kind, alloc₀⟩
      dsimp only at hslice hwrite hbyteSize hmask' hslice'
      obtain ⟨hnodup', hlive', hother⟩ := hset_prop ⟨kind, alloc'⟩
      let mach' := inplaceMachine m.machine allocIdx allocId kind alloc'
      have hoff_eq : Miri.ABI.Size.ofBytes (elemMp.ptr.offset.bytes - baseAddr) =
          Miri.ABI.Size.ofBytes (relOffset.bytes + UInt64.ofNat ((fromIdx + off) * es.bytes.toNat)) := by
        have hb : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
        dsimp only [elemMp]
        simp only [Miri.ABI.Size.ofBytes, hb, uint64_add_add_sub_cancel_left]
      dsimp only [es, elemLay, elemTy] at hoff_eq
      have hmsc_sz : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).size = msc.size := rfl
      have hprov_e : elemMp.ptr.provenance = some (.concrete allocId tag) := hprov
      have hw_ok : annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc)) ⟨.memory elemMp, elemLay⟩ m₀ =
          .ok () { stack := ⟨#[topFrame']⟩, machine := mach' } := by
        unfold annealWriteImmediateLM2_2 annealWriteIndirectImmediate
        simp only [m₀, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
          stack_currentFrame?_singleton ⟨#[topFrame']⟩ topFrame' rfl, hprov_e, Option.bind_some,
          Miri.Memory.Provenance.getAllocId, hbase, hfindIdx, hgetIdx, add_size_zero_bytes,
          hoff_eq, hmsc_sz, hwrite, pure, EStateM.pure, set, MonadStateOf.set, EStateM.set]
        rfl
      have hm_stmt : Miri.Interpreter.Step.evalStatement
          (annealStepHooksLM2_4 body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨arrIdx, [.subslice fromIdx toIdx fromEnd,
            .constantIndex off minLen false]⟩ (.use (.constant c)), span⟩) m =
          ({ stack := ⟨#[topFrame']⟩, machine := mach' }, .ok ()) := by
        have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
            mirPlace true m = .ok ⟨.memory elemMp, elemLay⟩ m₀ := hplace_ok
        have hop_m' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
            (Miri.Interpreter.OperandPath.rvalue "operand")
            (translateOperand (.constant c))
            (some ((annealRvalueHooksLM2_4 body.localDecls body.layouts).placeLayout
              ⟨.memory elemMp, elemLay⟩)) m₀ =
            .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ m₀ := hop_m
        unfold Miri.Interpreter.Step.evalStatement translateStmt
        dsimp only [translateStmtKind]
        change (if lm24Assign body.localDecls body.layouts mirPlace
            (translateRvalue (.use (.constant c))) then _ else _) = _
        simp only [hlm24, ↓reduceIte]
        unfold Miri.Interpreter.runRvalue Miri.Interpreter.evalRvalueIntoPlace
        dsimp only [mirPlace] at hevalPlace'
        rw [EStateM.bind_eq_ok hevalPlace']
        dsimp only [translateRvalue]
        rw [EStateM.bind_eq_ok hop_m']
        simp only [annealRvalueHooksLM2_4, usesMemCopy, Bool.false_eq_true, ↓reduceIte,
          annealRvalueHooksLM2_2, annealReadImmediateLM2_2, bind, EStateM.bind, pure, EStateM.pure, hw_ok]
      have hloc' : topFrame'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
        hframe.location_eq
      have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
        hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl hloc'
      have hwp := writeProjectedForLocal_subslice_constIndex s.frame.locals body.localDecls
        body.layouts arrIdx elems (.scalar sc) hslice.elems_len hin hoff_lt hmin_le
      let locals₂ :=
        s.frame.locals.set arrIdx (.init (.aggregate 0 (elems.set (fromIdx + off) (.scalar sc))))
      have ha_ok : evalStmt s
          ⟨.assign ⟨arrIdx, [.subslice fromIdx toIdx fromEnd, .constantIndex off minLen false]⟩
            (.use (.constant c)), span⟩ body.localDecls body.layouts =
          MirStepNode.step (advanceStmt s locals₂ s.memory) := by
        unfold evalStmt; dsimp only; rw [ha_rv]; dsimp only
        rw [hinit]; dsimp only
        rw [hwp]; dsimp only
        rw [set?_eq_some_set hlt_af_arr, hprot, hbor]
        dsimp only [invalidateConflictingBorrowsAtProj]
        rw [hmem_same]
      have hmp' : MemPlaceRel mach' arrDecl.ty body.layouts
          (some (.aggregate 0 (elems.set (fromIdx + off) (.scalar sc)))) mp := by
        refine .mk allocId tag baseAddr relOffset ⟨kind, alloc'⟩
          hprov hmis hmeta hlive' hbase hno_ovf0 hptr hslice'.alloc_mut haligned
          (by dsimp only; rw [hbyteSize]; exact hin_arr)
          (fun h => nomatch h)
          (fun _ _ hnz => by dsimp only; rw [hmask']; exact hval_cons (.aggregate 0 elems) rfl hnz)
          (fun _ h => nomatch h)
          (fun ek cnt' es' hk hopt => ?_)
        rw [hwf.arr_kind] at hk
        injection hk with hek hcnt'; subst hek hcnt'
        injection hopt with hagg; injection hagg with _ hes'; subst hes'
        exact ⟨hwf.arr_fields, hwf.arr_size, hwf.arr_align, hslice'⟩
      have hframe₀ : FrameRelLM2_4 body m.machine s.frame topFrame' :=
        hframe.cache_local_layout hdecl_arr hlt_arr
      have hdisj₀ : MemoryAllocDisjoint topFrame' := hdisj.cache_layout hlt_arr arrLay
      have hmls_arr' : topFrame'.locals[arrIdx]? = some ⟨.live (.indirect mp), some arrLay⟩ := by
        dsimp only [topFrame', cacheFrameLocalLayout]
        rw [Array.getElem?_set_self, hmls_arr_eq]
      let tf_fin := { topFrame' with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
      let m' : AnnealStepState := { stack := ⟨#[tf_fin]⟩, machine := mach' }
      have hframe_fin : FrameRelLM2_4 body mach' (advanceStmt s locals₂ s.memory).frame tf_fin :=
        { body_eq := hframe₀.body_eq
          location_eq := rfl
          af_locals_len := by
            show (s.frame.locals.set arrIdx _).length = _
            rw [List.length_set]; exact hframe.af_locals_len
          mf_locals_size := hframe₀.mf_locals_size
          locals_rel := by
            intro i decl slot mls hdecl hslot hmls
            have hslot' : get? locals₂ i = some slot := hslot
            have hmls' : topFrame'.locals[i]? = some mls := hmls
            rw [get?_eq_getElem?, List.getElem?_set] at hslot'
            by_cases hia : arrIdx = i
            · subst hia
              simp only [↓reduceIte, hlt_af_arr, Option.some.injEq] at hslot'
              subst hslot'
              rw [hmls_arr'] at hmls'; injection hmls' with hmls'; subst hmls'
              rw [hdecl_arr] at hdecl; cases hdecl
              exact .base _ _ (.indirect _ mp _
                (fun l hl => (Option.some.inj hl).symm) nofun hmp')
            · simp only [hia, ↓reduceIte] at hslot'
              have hloc := hframe₀.locals_rel i decl slot mls hdecl hslot' hmls'
              refine hloc.of_entry ?_
              intro mp_i c_i hmi a la' hpa hla'
              subst hmi
              have hne_a : a ≠ allocId := by
                intro hae; subst hae
                have hd := hdisj₀ arrIdx i mp mp_i (some arrLay) c_i hia hmls_arr' hmls'
                rw [hprov, hpa] at hd; exact hd rfl
              exact ⟨hother a la' hne_a hla', rfl⟩ }
      have hstate' : StateRelLM2_4 body (advanceStmt s locals₂ s.memory) m' :=
        StateRelLM2_4.mk tf_fin rfl hretCont ⟨retLay, hretPlace⟩ hframe_fin hcal hstack hbor hprot
          hcaller hdisj₀
      refine ⟨advanceStmt s locals₂ s.memory, m', mp, by rw [hstep_a, ha_ok], hstep_m, hstate',
        ?_, hmp', hnodup', ?_⟩
      · simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_arr]
      · intro _ hw0 _
        obtain ⟨hw', hnext⟩ := MemoryHighWater.inplaceMachine (allocIdx := allocIdx) (kind := kind)
          (alloc := alloc') hw0 hlive
        exact ⟨hw', by rw [hnext]; omega⟩

/-- **`step_repeat_union_field_simulation`** (`LM-2.4`): array repeat
`_arr = [copy u.j; count]` or `_arr = [move u.j; count]`
(`Rvalue.Repeat (unionFieldReadOperand isMove u j fty) count`) on `StateRelLM2_4`,
exercising `annealRvalueHooksLM2_4.writeRepeat` (`annealAggregateHooksLM2_4`)
where `_u` is a union of `S` bytes holding field `0`'s value `sc` (`UnionMemRel`)
and `_arr` has array type `[elemKind; count]`:

1. **Wider uninitialized union field (`1 ≤ j`, `sc.sizeBytes < w ≤ S`)**: both
   Anneal and `lean-miri` report undefined behavior while reading the repeat
   element (`StepRelLM2_4.ub`).
2. **Initialized union field (`j = 0`, `fty = f0Ty`) into `.dead` `_arr`**: both
   Anneal and `lean-miri` report undefined behavior (`StepRelLM2_4.ub`).
3. **Initialized union field (`j = 0`, `fty = f0Ty`) into `.uninit` immediate
   `_arr` with `CanReserveAllocId m.machine.memory`**: both machines step in
   lockstep (`StateRelLM2_4`), populating `_arr` with
   `List.replicate count (.scalar sc)` (`MemPlaceRel`), preserving `_u`'s
   `UnionMemRel`, `LiveAllocsNodup`, and `StepPreservesHighWater m 1`. -/
theorem step_repeat_union_field_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {arrIdx u : Local} {j : Nat} {fty : Ty} {isMove : Bool}
    {count : Nat} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨arrIdx, .nil⟩ (.repeat (unionFieldReadOperand isMove u j fty) count), span⟩)
    {arrDecl uDecl : LocalDecl} {elemKind : RigidTy}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hprim : IsPrimScalarTy fty) {w : Nat} (hw : ValidScalarBytes w)
    (hsz : (translateTy fty body.layouts).layout.size = translateSizeBytes w)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n) (hj : j < n)
    {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp_u), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp_u)
    (hf0_eq : f0Ty = { kind := elemKind, layoutIdx := 0 })
    (hbool : elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)
    (hfl : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size := by exact ⟨_, rfl, rfl⟩) :
    (j ≠ f → sc.sizeBytes < w → w ≤ S →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (j = f → fty = f0Ty → get? s.frame.locals arrIdx = some .dead →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (j = f → fty = f0Ty →
      get? s.frame.locals arrIdx = some .uninit →
      (∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf arrIdx) →
      CanReserveAllocId m.machine.memory →
      ∃ (s' : MachineState) (m' : AnnealStepState) (mp_arr : Miri.Interpreter.MemPlace AnnealProv)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        stepMirFn body s = .step s' ∧
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals arrIdx =
          some (.init (.aggregate 0 (List.replicate count (.scalar sc)))) ∧
        get? s'.frame.locals u =
          some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) ∧
        m'.stack.frames = #[tf'] ∧
        MemPlaceRel m'.machine arrDecl.ty body.layouts
          (some (.aggregate 0 (List.replicate count (.scalar sc)))) mp_arr ∧
        UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty sc mp_u ∧
        LiveAllocsNodup m'.machine ∧
        StepPreservesHighWater m 1 (m', .ok true)) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem; dsimp only at hbor hprot; subst hbor hprot; rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨arrIdx, .nil⟩ (.repeat (unionFieldReadOperand isMove u j fty) count), span⟩
      body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
  obtain ⟨slot_arr, mls_arr, hlt_af_arr, hlt_arr0, hslot_arr, hmls_arr, hmls_arr_eq, hloc_arr⟩ :=
    hframe.lookup_local hdecl_arr
  obtain ⟨_, mls_u, _, hlt_u, _, hmls_u', hmls_u_eq, hloc_u⟩ := hframe.lookup_local hdecl_u
  obtain ⟨c_u, hmls_u⟩ := hu_mls topFrame hframes
  rw [hmls_u] at hmls_u'; injection hmls_u' with hmls_u'; subst hmls_u'
  have hcache_arr : ∀ l, (topFrame.locals[arrIdx]'hlt_arr0).layout = some l →
      l = translateTy arrDecl.ty body.layouts := by
    rw [hmls_arr_eq]; exact hloc_arr.layout_eq
  have harr_ne_u : arrIdx ≠ u := by
    intro heq; subst heq
    rw [hdecl_arr] at hdecl_u; injection hdecl_u with hdecl_u; subst hdecl_u
    obtain ⟨_, hn, _⟩ := hwt.fields_union
    rw [hwf.arr_fields] at hn; cases hn
  let arrLay := translateTy arrDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame arrIdx hlt_arr0 arrLay
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 arrIdx none topFrame.localsIdentity, arrLay⟩
  have hevalPlace_dst : annealEvalPlaceLM2_4 body.localDecls body.layouts ⟨arrIdx, #[]⟩ m =
      .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_arr0 hdecl_arr hcache_arr
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀, cacheFrameLocalLayout]; rw [Array.size_set]; exact hlt_u
  have hu₀' : topFrame₀.locals[u]? = some ⟨.live (.indirect mp_u), c_u⟩ := by
    dsimp only [topFrame₀, cacheFrameLocalLayout]
    rw [Array.getElem?_set_ne _ harr_ne_u]
    exact hmls_u
  have hu₀_eq : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp_u), c_u⟩ := by
    have h := Array.getElem?_eq_getElem hlt_u₀
    rw [hu₀'] at h
    exact (Option.some.inj h).symm
  have hcache_u : ∀ l, (topFrame₀.locals[u]'hlt_u₀).layout = some l →
      l = translateTy uDecl.ty body.layouts := by
    rw [hu₀_eq]; exact hloc_u.layout_eq
  have hu₀ : (topFrame₀.locals[u]'hlt_u₀).value = .live (.indirect mp_u) := by
    rw [hu₀_eq]
  have hmeta : mp_u.metadata = .none := by
    cases hmem with | mk _ _ _ _ _ _ _ hm => exact hm
  obtain ⟨msc0, hk_le0, hprim0, himm0⟩ :
      ∃ msc0, sc.sizeBytes ≤ S ∧ IsPrimScalarTy f0Ty ∧
        ImmediateRel f0Ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc0)) := by
    cases hmem with
    | mk _ _ _ _ msc0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hkle _ _ hp0 hi0 _ =>
      exact ⟨msc0, hkle, hp0, hi0⟩
  have hop_spec := evalOperand_unionFieldRead_spec (globals := s.memory.globals) (isMove := isMove)
    hdecl_u hprim hw hsz hwt hfields hf hj hprim0 himm0 hk_le0 hfl hu_slot
  let topFrame₁ := cacheFrameLocalLayout topFrame₀ u hlt_u₀ (translateTy uDecl.ty body.layouts)
  let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
  have hop_u : annealEvalOperandLM2_4 body.localDecls body.layouts
      (translateOperand (unionFieldReadOperand isMove u j fty)) none m₀ =
      .ok ⟨.indirect mp_u, translateTy fty body.layouts⟩ m₁ := by
    have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
    have hfield := annealEvalUnionField_indirect (body := body) (m := m₀) rfl hlt_u₀ hdecl_u
      hcache_u (by rw [hu₀]) hmeta hfields hj hprim
    cases isMove <;>
      simp only [unionFieldReadOperand, translateOperand, translatePlace, List.map,
        translateProjectionElem, List.toArray, annealEvalOperandLM2_4, hunion, ↓reduceIte,
        Bool.false_eq_true] <;>
      exact hfield
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨arrIdx, #[]⟩
      (translateRvalue (.repeat (unionFieldReadOperand isMove u j fty) count)) = true := by
    have hunion := isUnionLocal_of_wellTyped hdecl_u hwt
    cases isMove <;>
      simp [lm24Assign, lm24Rvalue, lm24Operand, lm24Place, translateRvalue, translateOperand,
        unionFieldReadOperand, translatePlace, hunion]
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨arrIdx, .nil⟩
        (.repeat (unionFieldReadOperand isMove u j fty) count), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.writeRepeat (annealAggregateHooksLM2_4 body.localDecls body.layouts) ()
          (translateOperand (unionFieldReadOperand isMove u j fty)) destPlace) m₀ := by
    have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
        ⟨arrIdx, #[]⟩ true m = .ok destPlace m₀ := hevalPlace_dst
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace']
    rfl
  obtain ⟨hsame, hbig⟩ := annealReadImmediate_unionMem (m := m₁) hnodup hwt.size_valid hmem
    hprim hw hsz
  obtain ⟨hf0sz, hkv⟩ := hmem.f0_size
  refine ⟨fun hjne hk_lt hw_le => ?_, fun hjf hty hdead => ?_,
    fun hjf hty huninit harr_imm hcanRes => ?_⟩
  · -- (1) Wider uninitialized union field (`j ≠ f`, `sc.sizeBytes < w ≤ S`).
    have hev_ub := hop_spec.2.2 hjne hk_lt hw_le
    have ha_ub : evalStmt s
        ⟨.assign ⟨arrIdx, .nil⟩ (.repeat (unionFieldReadOperand isMove u j fty) count), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue; dsimp only; rw [hbor, hcaller, hev_ub]
    have hread_err := hbig hk_lt hw_le
    have hop_agg_err : (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
        (Miri.Interpreter.OperandPath.rvalue "operand")
        (translateOperand (unionFieldReadOperand isMove u j fty)) none m₀ =
        .error (.undefinedBehavior "read of uninitialized memory field") m₁ := by
      dsimp only [annealAggregateHooksLM2_4]
      rw [EStateM.bind_eq_ok hop_u, EStateM.bind_eq_error hread_err]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨arrIdx, .nil⟩
          (.repeat (unionFieldReadOperand isMove u j fty) count), span⟩) m =
        (m₁, .error (.undefinedBehavior "read of uninitialized memory field")) := by
      rw [hm_eval, writeRepeat_def]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error hop_agg_err]
    rw [hstep_a, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_err]
    exact .ub _ _
  · -- (2) Initialized union field (`j = f`, `fty = f0Ty`) into `.dead` `_arr`.
    have hev_ok := hop_spec.1 hjf hty
    simp only [hjf, ← hty] at *
    have hwk : w = sc.sizeBytes :=
      translateSizeBytes_inj hw hkv (hsz.symm.trans hf0sz)
    obtain ⟨msc, hrel_sc, _, hread_ok⟩ := hsame hwk
    have ha_ub : evalStmt s
        ⟨.assign ⟨arrIdx, .nil⟩ (.repeat (unionFieldReadOperand isMove u f fty) count), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue; dsimp only; rw [hbor, hcaller, hev_ok]; dsimp only
      rw [replicateValue_eq_replicate, hdead]
    have hop_agg_ok : (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
        (Miri.Interpreter.OperandPath.rvalue "operand")
        (translateOperand (unionFieldReadOperand isMove u f fty)) none m₀ =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy fty body.layouts⟩ m₁ := by
      dsimp only [annealAggregateHooksLM2_4]
      rw [EStateM.bind_eq_ok hop_u, EStateM.bind_eq_ok hread_ok]; rfl
    rw [hdead] at hslot_arr; injection hslot_arr with hse; subst hse
    have hdead_val := hloc_arr.dead_value
    have hlt_arr₁ : arrIdx < topFrame₁.locals.size := by
      dsimp only [topFrame₁, topFrame₀]
      rw [cacheFrameLocalLayout_size, cacheFrameLocalLayout_size]; exact hlt_arr0
    have hval_arr₁ : (topFrame₁.locals[arrIdx]'hlt_arr₁).value = .dead := by
      have h : topFrame₁.locals[arrIdx]? = some ⟨.dead, some arrLay⟩ := by
        dsimp only [topFrame₁, cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ (Ne.symm harr_ne_u)]
        dsimp only [topFrame₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set_self, hmls_arr_eq, hdead_val]
      have h' := Array.getElem?_eq_getElem hlt_arr₁
      rw [h] at h'
      exact congrArg Miri.Interpreter.LocalState.value (Option.some.inj h').symm
    have hens_err := annealEnsureAllocated_dead (m := m₁) (tf := topFrame₁)
      (id := topFrame.localsIdentity) (lay := arrLay) rfl hlt_arr₁ hval_arr₁
    have hforce_err : (annealAggregateHooksLM2_4 body.localDecls body.layouts).forceAllocation ()
        destPlace m₁ = .error (.undefinedBehavior "write to dead local") m₁ := by
      dsimp only [annealAggregateHooksLM2_4, annealAggregateHooksLM2_2, destPlace]
      exact EStateM.bind_eq_error hens_err
    have hisSized : (translateTy fty body.layouts).layout.isSized = true := hprim.isSized
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨arrIdx, .nil⟩
          (.repeat (unionFieldReadOperand isMove u f fty) count), span⟩) m =
        (m₁, .error (.undefinedBehavior "write to dead local")) := by
      rw [hm_eval, writeRepeat_def]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hop_agg_ok]; dsimp only
      rw [hisSized]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [EStateM.bind_eq_error hforce_err]
    rw [hstep_a, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_err]
    exact .ub _ _
  · -- (3) Initialized union field (`j = f`, `fty = f0Ty`) into `.uninit` immediate `_arr`.
    have hev_ok := hop_spec.1 hjf hty
    simp only [hjf, ← hty] at *
    have hwk : w = sc.sizeBytes :=
      translateSizeBytes_inj hw hkv (hsz.symm.trans hf0sz)
    obtain ⟨msc, hrel_sc, _, hread_ok⟩ := hsame hwk
    let locals₂ :=
      s.frame.locals.set arrIdx (.init (.aggregate 0 (List.replicate count (.scalar sc))))
    have ha_ok : evalStmt s
        ⟨.assign ⟨arrIdx, .nil⟩ (.repeat (unionFieldReadOperand isMove u f fty) count), span⟩
        body.localDecls body.layouts =
        MirStepNode.step (advanceStmt s locals₂ s.memory) := by
      unfold evalStmt evalRvalue; dsimp only; rw [hbor, hcaller, hev_ok]; dsimp only
      rw [replicateValue_eq_replicate, hprot, hbor]
      dsimp only [invalidateConflictingBorrows]
      rw [hmem_same, huninit]
      simp [set?_eq_some_set hlt_af_arr, locals₂]
    have hop_agg_ok : (annealAggregateHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
        (Miri.Interpreter.OperandPath.rvalue "operand")
        (translateOperand (unionFieldReadOperand isMove u f fty)) none m₀ =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy fty body.layouts⟩ m₁ := by
      dsimp only [annealAggregateHooksLM2_4]
      rw [EStateM.bind_eq_ok hop_u, EStateM.bind_eq_ok hread_ok]; rfl
    rw [huninit] at hslot_arr; injection hslot_arr with hse; subst hse
    have harr_imm' := harr_imm topFrame hframes mls_arr hmls_arr
    have himm_val0 : mls_arr.value = .live (.immediate .uninit) := by
      cases hloc_arr with
      | base _ _ hl =>
        cases hl with
        | indirect _ mp' _ _ _ _ => exact absurd rfl (harr_imm' mp')
        | immediate _ _ _ _ hv =>
          rcases hv with ⟨_, rfl⟩ | ⟨_, h, _⟩
          · rfl
          · cases h
    have hlt_arr₁ : arrIdx < topFrame₁.locals.size := by
      dsimp only [topFrame₁, topFrame₀]
      rw [cacheFrameLocalLayout_size, cacheFrameLocalLayout_size]; exact hlt_arr0
    have hmls_arr₁ : topFrame₁.locals[arrIdx]'hlt_arr₁ = ⟨.live (.immediate .uninit), some arrLay⟩ := by
      have h : topFrame₁.locals[arrIdx]? = some ⟨.live (.immediate .uninit), some arrLay⟩ := by
        dsimp only [topFrame₁, cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ (Ne.symm harr_ne_u)]
        dsimp only [topFrame₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set_self, hmls_arr_eq, himm_val0]
      have h' := Array.getElem?_eq_getElem hlt_arr₁
      rw [h] at h'
      exact (Option.some.inj h').symm
    have hval_arr₁ : (topFrame₁.locals[arrIdx]'hlt_arr₁).value = .live (.immediate .uninit) := by
      rw [hmls_arr₁]
    have hc_arr₁ : (topFrame₁.locals[arrIdx]'hlt_arr₁).layout = some arrLay := by
      rw [hmls_arr₁]
    obtain ⟨mem', allocId, hres⟩ := hcanRes
    obtain ⟨alloc₀, hens_ok, hsize₀, _, _, _, hslice₀⟩ :=
      annealEnsureAllocated_immediate
        (m := m₁) (tf := topFrame₁) (id := topFrame.localsIdentity)
        (arrTy := arrDecl.ty) (layouts := body.layouts) (elemKind := elemKind)
        rfl hlt_arr₁ hval_arr₁ hres
    obtain ⟨hlive_eq, hfresh₀⟩ := reserveAllocId_ok_live hres
    have hfresh : mem'.live.any (fun entry => entry.1 == allocId) = false := by
      rw [hlive_eq]; exact hfresh₀
    have hsz_elem : (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size =
        translateSizeBytes sc.sizeBytes := by
      rw [← hf0_eq]; exact hf0sz
    let tf₃ := setFrameLocalIndirect topFrame₁ arrIdx hlt_arr₁ (stackAllocPlace allocId)
    obtain ⟨alloc_final, hbody_ok, hsize_final, hslice_final⟩ :=
      writeRepeat_after_forceAlloc_spec (body := body) (mach := m.machine) (mem' := mem')
        (allocId := allocId) (alloc₀ := alloc₀) (tf := tf₃)
        (arrTy := arrDecl.ty) (elemKind := elemKind) (count := count)
        (sc := sc) (msc := msc)
        (srcLay := translateTy fty body.layouts)
        hwf hfresh hrel_sc hsz_elem hbool hchar hsize₀ hslice₀
    have hforce_ok :
        (annealAggregateHooksLM2_4 body.localDecls body.layouts).forceAllocation () destPlace m₁ =
        .ok ⟨.memory (stackAllocPlace allocId), arrLay⟩
          { stack := ⟨#[tf₃]⟩, machine := stackAllocMachine m.machine mem' allocId alloc₀ } := by
      dsimp only [annealAggregateHooksLM2_4, annealAggregateHooksLM2_2, destPlace]
      rw [EStateM.bind_eq_ok hens_ok]; rfl
    have hisSized : (translateTy fty body.layouts).layout.isSized = true := hprim.isSized
    let mach₃ := stackAllocMachine m.machine mem' allocId alloc_final
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨arrIdx, .nil⟩
          (.repeat (unionFieldReadOperand isMove u f fty) count), span⟩) m =
        ({ stack := ⟨#[tf₃]⟩, machine := mach₃ }, .ok ()) := by
      rw [hm_eval, writeRepeat_def]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hop_agg_ok]; dsimp only
      rw [hisSized]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [EStateM.bind_eq_ok hforce_ok]
      have hbody_ok' :
          (do
            let length ← (annealAggregateHooksLM2_4 body.localDecls body.layouts).length ()
              ⟨.memory (stackAllocPlace allocId), arrLay⟩
            if length == 0 then
              (annealAggregateHooksLM2_4 body.localDecls body.layouts).getPlaceAllocMut ()
                ⟨.memory (stackAllocPlace allocId), arrLay⟩
            else
              let first ← (annealAggregateHooksLM2_4 body.localDecls body.layouts).projectIndex ()
                ⟨.memory (stackAllocPlace allocId), arrLay⟩ 0
              (annealAggregateHooksLM2_4 body.localDecls body.layouts).copyOp ()
                ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy fty body.layouts⟩ first
              let elemSize := ((annealAggregateHooksLM2_4 body.localDecls body.layouts).placeLayout first).layout.size
              let firstPtr ← aggregateLiftPub ((annealAggregateHooksLM2_4 body.localDecls body.layouts).placePointer first)
              let restPtr ← aggregateLiftPub ((annealAggregateHooksLM2_4 body.localDecls body.layouts).wrappingOffset firstPtr elemSize)
              (annealAggregateHooksLM2_4 body.localDecls body.layouts).memCopyRepeatedly () firstPtr restPtr elemSize (length - 1) true)
            { stack := ⟨#[tf₃]⟩, machine := stackAllocMachine m.machine mem' allocId alloc₀ } =
          .ok () { stack := ⟨#[tf₃]⟩, machine := mach₃ } := hbody_ok
      rw [hbody_ok']
    have hloc_tf₃ : tf₃.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hframe.location_eq
    have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
      hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl hloc_tf₃
    obtain ⟨hlive_b, hfreshne, hbase_b⟩ :=
      stackAllocMachine_live_base (mach := m.machine) alloc_final hres
    let mp_arr := stackAllocPlace allocId
    have hmp_arr : MemPlaceRel mach₃ arrDecl.ty body.layouts
        (some (.aggregate 0 (List.replicate count (.scalar sc)))) mp_arr := by
      refine stackAlloc_memPlaceRel hslice_final.alloc_mut
        (translateTy_align_pow2_le_29 arrDecl.ty body.layouts)
        hsize_final
        (fun h => nomatch h)
        (fun _ _ _ => ?_)
        (fun _ h => nomatch h)
        (fun ek cnt' es' hk hopt => ?_)
      · rw [hslice_final.alloc_mask, hsize_final]
        have hend_a : (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy arrDecl.ty body.layouts).layout.size).endExclusive =
            .ok (translateTy arrDecl.ty body.layouts).layout.size := by
          have hlt0 : Miri.ABI.Size.ZERO.bytes.toNat +
              (translateTy arrDecl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64 := by
            simp [Miri.ABI.Size.ZERO]; exact UInt64.toNat_lt _
          have h := allocRange_endExclusive_of_lt (off := Miri.ABI.Size.ZERO)
            (sz := (translateTy arrDecl.ty body.layouts).layout.size) hlt0
          simpa [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes] using h
        exact Miri.Memory.InitMask.lazy_initialized_query _ _ _ hend_a (UInt64.le_refl _)
      · rw [hwf.arr_kind] at hk
        injection hk with hek hcnt'; subst hek hcnt'
        injection hopt with hagg; injection hagg with _ hes'; subst hes'
        exact ⟨hwf.arr_fields, hwf.arr_size, hwf.arr_align, hslice_final⟩
    have hframe₁ : FrameRelLM2_4 body m.machine s.frame topFrame₁ :=
      (hframe.cache_local_layout hdecl_arr hlt_arr0).cache_local_layout hdecl_u hlt_u₀
    have hdisj₁ : MemoryAllocDisjoint topFrame₁ :=
      (hdisj.cache_layout hlt_arr0 _).cache_layout hlt_u₀ _
    let tf_fin := { tf₃ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
    let m' : AnnealStepState := { stack := ⟨#[tf_fin]⟩, machine := mach₃ }
    have hframe_fin : FrameRelLM2_4 body mach₃ (advanceStmt s locals₂ s.memory).frame tf_fin :=
      { body_eq := hframe₁.body_eq
        location_eq := rfl
        af_locals_len := by
          show (s.frame.locals.set arrIdx _).length = _
          rw [List.length_set]; exact hframe.af_locals_len
        mf_locals_size := by
          show (topFrame₁.locals.set arrIdx _ hlt_arr₁).size = _
          rw [Array.size_set]; exact hframe₁.mf_locals_size
        locals_rel := by
          intro i decl slot mls hdecl hslot hmls
          have hslot' : get? locals₂ i = some slot := hslot
          have hmls' : (topFrame₁.locals.set arrIdx
              { topFrame₁.locals[arrIdx]'hlt_arr₁ with value := .live (.indirect mp_arr) }
              hlt_arr₁)[i]? = some mls := hmls
          rw [get?_eq_getElem?, List.getElem?_set] at hslot'
          rw [Array.getElem?_set] at hmls'
          by_cases hid : arrIdx = i
          · subst hid
            simp only [↓reduceIte, hlt_af_arr, Option.some.injEq] at hslot' hmls'
            subst hslot' hmls'
            rw [hdecl_arr] at hdecl; cases hdecl
            refine .base _ _ (.indirect
              (.init (.aggregate 0 (List.replicate count (.scalar sc)))) mp_arr _ ?_ nofun hmp_arr)
            intro l hl; rw [hc_arr₁] at hl; exact (Option.some.inj hl).symm
          · simp only [hid, ↓reduceIte] at hslot' hmls'
            exact (hframe₁.locals_rel i decl slot mls hdecl hslot' hmls').of_live_base hlive_b
              hbase_b }
    have hdisj_fin : MemoryAllocDisjoint tf_fin := by
      intro i j mp_i mp_j lay_i lay_j hij hi hj
      dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hi hj
      rw [Array.getElem?_set] at hi hj
      by_cases hi_a : arrIdx = i
      · subst hi_a
        have hj_a : arrIdx ≠ j := hij
        simp only [hj_a, ↓reduceIte] at hj
        simp only [↓reduceIte] at hi
        obtain ⟨a, la', ha, hla⟩ := hframe₁.indirect_allocId hj
        injection hi with hi; injection hi with hv _; injection hv with hv; injection hv with hv
        subst hv; rw [ha]
        simp only [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
          Option.some.injEq]
        exact fun h => hfreshne a la' hla h.symm
      · simp only [hi_a, ↓reduceIte] at hi
        by_cases hj_a : arrIdx = j
        · subst hj_a
          simp only [↓reduceIte] at hj
          obtain ⟨a, la', ha, hla⟩ := hframe₁.indirect_allocId hi
          injection hj with hj; injection hj with hv _; injection hv with hv; injection hv with hv
          subst hv; rw [ha]
          simp only [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
            Option.some.injEq]
          exact hfreshne a la' hla
        · simp only [hj_a, ↓reduceIte] at hj
          exact hdisj₁ i j mp_i mp_j lay_i lay_j hij hi hj
    have hstate' : StateRelLM2_4 body (advanceStmt s locals₂ s.memory) m' :=
      StateRelLM2_4.mk tf_fin rfl hretCont ⟨retLay, hretPlace⟩
        hframe_fin hcal hstack hbor hprot hcaller hdisj_fin
    refine ⟨advanceStmt s locals₂ s.memory, m', mp_arr, tf_fin, by rw [hstep_a, ha_ok],
      hstep_m, hstate', ?_, ?_, rfl, hmp_arr, hmem.of_live_base hlive_b hbase_b,
      LiveAllocsNodup.stackAllocMachine alloc_final hnodup hres,
      fun _ hw0 hb0 => MemoryHighWater.stackAllocMachine alloc_final hw0 hb0 hres⟩
    · simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_arr]
    · simp only [advanceStmt, locals₂, get?_eq_getElem?, List.getElem?_set_ne harr_ne_u]
      exact hu_slot

/-! ## 18. `StorageLive` and `StorageDead` on `StateRelLM2_4`

`step_storageLive_LM2_4_simulation` and `step_storageDead_LM2_4_simulation`
prove lockstep simulation of `StatementKind.storageLive` and
`StatementKind.storageDead` under `annealStepHooksLM2_4` on `StateRelLM2_4`,
including freeing any backing union (`UnionMemRel`) or array (`MemPlaceRel`)
stack allocation while preserving `StateRelLM2_4`, `StepPreservesNodup`, and
`StepPreservesHighWater m 0`. -/

/-- A local related by `UnionLocalRel` owns, if anything, a live allocation. -/
theorem UnionLocalRel.allocLive {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : UnionLocalRel mach decl layouts slot mls) :
    LocalAllocLive mach.memory mls.value := by
  cases h with
  | base _ _ hl => exact hl.allocLive
  | union _ _ _ _ _ mp _ _ _ _ _ hmem =>
    intro mp' hv
    injection hv with hv; injection hv with hv; subst hv
    cases hmem with
    | mk allocId tag _ localAlloc _ hprov _ _ hl _ =>
      refine ⟨allocId, by rw [hprov]; rfl, ?_⟩
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hl
      rw [Array.any_eq_true]
      refine ⟨i, by simpa using hi, ?_⟩
      simp only [Array.getElem_toList] at hget
      simp [hget]

/-- Removing an allocation `id` from `memory.live` preserves every `UnionMemRel`
whose provenance names a different allocation. -/
theorem UnionMemRel.of_filter_live {mach : AnnealMachine} {id : Miri.Memory.AllocId}
    {uTy : Ty} {layouts : LayoutTable} {S : Nat} {f0Ty : Ty} {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : UnionMemRel mach uTy layouts S f0Ty sc mp)
    (hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id) :
    UnionMemRel { mach with memory := { mach.memory with
        live := mach.memory.live.filter (fun entry => entry.1 != id) } }
      uTy layouts S f0Ty sc mp := by
  cases h with
  | mk allocId tag baseAddr localAlloc msc hprov hmis hmeta hl hb hptr hovf hsz hlen hmut
      hprovMap halign hextra hnative hk hmask hsc hprim himm hraw =>
    have hne' : allocId ≠ id := by
      intro heq; apply hne; rw [hprov, heq]; rfl
    refine .mk allocId tag baseAddr localAlloc msc hprov hmis hmeta ?_ hb hptr hovf hsz hlen hmut
      hprovMap halign hextra hnative hk hmask hsc hprim himm hraw
    simp only [Array.toList_filter, List.mem_filter]
    exact ⟨hl, by simp [hne']⟩

/-- Deallocating the allocation of one local preserves `UnionLocalRel` on every
local that owns a different allocation. -/
theorem UnionLocalRel.of_dealloc {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {v : Miri.Interpreter.LocalValue AnnealProv}
    (h : UnionLocalRel mach decl layouts slot mls)
    (hdisj : ∀ mp mp', v = .live (.indirect mp) → mls.value = .live (.indirect mp') →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp'.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    UnionLocalRel { mach with memory := deallocLocalMemory mach.memory v } decl layouts slot mls := by
  cases h with
  | base _ _ hl => exact .base _ _ (hl.of_dealloc hdisj)
  | union S n f f0Ty sc mp' c hc hwt hfields hf hmem =>
    refine .union S n f f0Ty sc mp' c hc hwt hfields hf ?_
    match v, hdisj with
    | .live (.indirect mp), hdisj =>
      have hd := hdisj mp mp' rfl rfl
      cases hid : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none =>
        have hmem_eq : deallocLocalMemory mach.memory (.live (.indirect mp)) = mach.memory := by
          simp only [deallocLocalMemory, hid]
        rw [hmem_eq]; exact hmem
      | some id =>
        have hmem_eq : deallocLocalMemory mach.memory (.live (.indirect mp)) =
            { mach.memory with live := mach.memory.live.filter (fun entry => entry.1 != id) } := by
          simp only [deallocLocalMemory, hid]
        rw [hmem_eq]
        exact hmem.of_filter_live (by rw [← hid]; exact Ne.symm hd)
    | .live (.immediate _), _ => exact hmem
    | .dead, _ => exact hmem

/-- `FrameRelLM2_4` update after deallocating the old value of local `idx`, given
`MemoryAllocDisjoint` for the old frame. -/
theorem FrameRelLM2_4.update_local_dealloc
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4 body mach af mf) (hdisj : MemoryAllocDisjoint mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot) (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : UnionLocalRel
      { mach with memory := deallocLocalMemory mach.memory (mf.locals[idx]'hlt_mf).value }
      decl body.layouts newSlot { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRelLM2_4 body
      { mach with memory := deallocLocalMemory mach.memory (mf.locals[idx]'hlt_mf).value }
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf }
    where
  body_eq := hrel.body_eq
  location_eq := hrel.location_eq
  af_locals_len := by rw [List.length_set, hrel.af_locals_len]
  mf_locals_size := by rw [Array.size_set, hrel.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    have hlt_af : idx < af.locals.length := by
      rw [hrel.af_locals_len, ← hrel.mf_locals_size]; exact hlt_mf
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i hmls_i
      have hdecl_eq : decl_i = decl := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
      subst hdecl_eq hslot_i hmls_i
      exact hnew
    · simp only [h_eq, ↓reduceIte] at hslot_i hmls_i
      apply (hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i).of_dealloc
      intro mp mp' hv hv'
      apply hdisj idx i mp mp' (mf.locals[idx]'hlt_mf).layout mls_i.layout h_eq
      · rw [Array.getElem?_eq_getElem hlt_mf, ← hv]
      · rw [hmls_i, ← hv']

/-- **`step_storageLive_LM2_4_simulation`** (`LM-2.4`): `StorageLive(loc)` on any
declared local `loc` in `StateRelLM2_4` (including an active memory-backed union
`UnionMemRel` or array `MemPlaceRel`): both machines make `loc` live and
uninitialized (`IsImmediateFrameLocal`), `lean-miri` frees any stack allocation
that `loc` previously owned (`deallocLocalMemory`), and `StateRelLM2_4`,
`StepPreservesNodup`, and `StepPreservesHighWater m 0` are preserved. -/
theorem step_storageLive_LM2_4_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl) :
    StepRelLM2_4 body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller,
      hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have ha : evalStmt s { kind := StatementKind.storageLive loc, span := span }
      body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc LocalSlot.uninit)) := by
    unfold evalStmt; dsimp only; rw [hslot, set?_eq_some_set hlt_af, ht_prot, ht_bor]
    dsimp only [disableLocalBorrows]
    congr 1; congr 1; cases hm_eq : s.memory; simp_all
  rw [ha]
  have hty : ∃ ty, topFrame.body.locals[loc]? = some ty := by
    rw [hfr.body_eq, translateBody_locals_getElem? body loc, hdecl]
    exact ⟨_, rfl⟩
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.storageLive loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind,
      annealStepHooksLM2_4]
    exact annealStepHooksLM2_2_storageLive_any_eq hframes hlt_mf hty hlive
  rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq]
  refine ⟨?_, StepPreservesNodup.of_nodup (hnodup.deallocLocalMemory _), ?_⟩
  · apply StepRelLM2_4.step
    have hnew : UnionLocalRel
        { m.machine with
          memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value }
        decl body.layouts .uninit
        { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } := by
      rw [hmls_eq]
      exact .base _ _ (.immediate .uninit .uninit mls.layout hloc.layout_eq (Or.inl ⟨rfl, rfl⟩))
    have hfr' := hfr.update_local_dealloc hdisj hdecl .uninit (.live (.immediate .uninit)) hnew
    exact StateRelLM2_4.mk _ rfl ht_ret ht_retp
      ⟨hfr'.body_eq, rfl, hfr'.af_locals_len, hfr'.mf_locals_size, hfr'.locals_rel⟩
      hcal_none ht_stack ht_bor ht_prot ht_caller (by
        apply MemoryAllocDisjoint.mono_immediate hdisj
        intro k
        by_cases hk : loc = k
        · subst hk
          right
          exact ⟨.uninit, (topFrame.locals[loc]'hlt_mf).layout, by
            simp only [Array.getElem?_set, ↓reduceIte]⟩
        · left
          simp only [hk, Array.getElem?_set, ↓reduceIte])
  · intro _ hw0 _
    obtain ⟨hw', hnext⟩ := MemoryHighWater.deallocLocalMemory hw0
      (topFrame.locals[loc]'hlt_mf).value
    exact ⟨hw', by rw [hnext]; omega⟩

/-- **`step_storageDead_LM2_4_simulation`** (`LM-2.4`): `StorageDead(loc)` on any
declared local `loc ≠ 0` in `StateRelLM2_4` (including an active memory-backed
union `UnionMemRel` or array `MemPlaceRel`): both machines mark `loc` dead,
`lean-miri` frees any stack allocation that `loc` owned (`deallocLocalMemory`),
and `StateRelLM2_4`, `StepPreservesNodup`, and `StepPreservesHighWater m 0` are
preserved. -/
theorem step_storageDead_LM2_4_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne : loc ≠ 0) :
    StepRelLM2_4 body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller,
      hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have ha : evalStmt s { kind := StatementKind.storageDead loc, span := span }
      body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc LocalSlot.dead)) := by
    unfold evalStmt; dsimp only; rw [hslot, set?_eq_some_set hlt_af, ht_prot, ht_bor]
    dsimp only [disableLocalBorrows]
    congr 1; congr 1; cases hm_eq : s.memory; simp_all
  rw [ha]
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.storageDead loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind,
      annealStepHooksLM2_4]
    exact annealStepHooksLM2_2_storageDead_any_eq hframes hlt_mf hne hlive
  rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq]
  refine ⟨?_, StepPreservesNodup.of_nodup (hnodup.deallocLocalMemory _), ?_⟩
  · apply StepRelLM2_4.step
    have hnew : UnionLocalRel
        { m.machine with
          memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value }
        decl body.layouts .dead
        { topFrame.locals[loc]'hlt_mf with value := .dead } := by
      rw [hmls_eq]
      exact .base _ _ (.dead mls.layout hloc.layout_eq)
    have hfr' := hfr.update_local_dealloc hdisj hdecl .dead .dead hnew
    exact StateRelLM2_4.mk _ rfl ht_ret ht_retp
      ⟨hfr'.body_eq, rfl, hfr'.af_locals_len, hfr'.mf_locals_size, hfr'.locals_rel⟩
      hcal_none ht_stack ht_bor ht_prot ht_caller (by
        apply MemoryAllocDisjoint.mono_dead hdisj
        intro k
        by_cases hk : loc = k
        · subst hk
          right
          exact ⟨(topFrame.locals[loc]'hlt_mf).layout, by
            simp only [Array.getElem?_set, ↓reduceIte]⟩
        · left
          simp only [hk, Array.getElem?_set, ↓reduceIte])
  · intro _ hw0 _
    obtain ⟨hw', hnext⟩ := MemoryHighWater.deallocLocalMemory hw0
      (topFrame.locals[loc]'hlt_mf).value
    exact ⟨hw', by rw [hnext]; omega⟩

end LeanMiriSpec.Correspondence
