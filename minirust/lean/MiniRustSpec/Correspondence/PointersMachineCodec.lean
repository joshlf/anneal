/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Interp

/-!
# Polymorphic `Machine<BM>` and `Mach` equivalence: codecs, validity, and unary operators

First of the four submodules of `MiniRustSpec.Correspondence.PointersMachine` (split purely
to bound per-process elaboration memory within an 8 GiB cgroup ceiling, keeping every public
declaration, name, and proof unchanged): byte/discriminant/value encoding, decoding, and
validity (`Type.decodeM_bm_eq`, `Type.encodeM_bm_eq`, `vtableFromPtrM_bm_eq`,
`checkValueM_bm_eq`), `ConcurrentMemory<BM>` loads/stores, and `evalUnOpM_bm_eq`.
-/

namespace MiniRustSpec.Correspondence

open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-! ## Unconditional equivalence of polymorphic `Machine<BM>` and `Mach` (`spec/lang/machine.md`) -/

namespace PointersMachineInternal

theorem bind_congr {α β : Type} {x y : Interp α} {f g : α → Interp β}
    (hxy : x = y) (hfg : ∀ a, f a = g a) :
    (x >>= f) = (y >>= g) := by
  subst hxy
  cases x with
  | error _ => rfl
  | ok a => exact hfg a

theorem bind_congr_right {α β : Type} (x : Interp α) {f g : α → Interp β}
    (hfg : ∀ a, f a = g a) :
    (x >>= f) = (x >>= g) :=
  bind_congr rfl hfg

theorem find?_eq_of_eq {α : Type} {p q : α → Bool} (h : ∀ x, p x = q x) :
    ∀ xs : List α, xs.find? p = xs.find? q
  | [] => rfl
  | x :: xs => by
    simp only [List.find?, h x]
    cases q x
    · exact find?_eq_of_eq h xs
    · rfl

theorem filter_eq_of_eq {α : Type} {p q : α → Bool} (h : ∀ x, p x = q x) :
    ∀ xs : List α, xs.filter p = xs.filter q
  | [] => rfl
  | x :: xs => by
    simp only [List.filter, h x]
    cases q x
    · exact filter_eq_of_eq h xs
    · exact congrArg (x :: ·) (filter_eq_of_eq h xs)

theorem map_eq_of_eq {α β : Type} {f g : α → β} (h : ∀ x, f x = g x) :
    ∀ xs : List α, xs.map f = xs.map g
  | [] => rfl
  | x :: xs => by simp only [List.map, h x, map_eq_of_eq h xs]

theorem abstractByte_dataM_bm_eq :
    AbstractByte.dataM (Provenance := Prov) = AbstractByte.data := by
  funext b; cases b <;> rfl


end PointersMachineInternal

open PointersMachineInternal

private theorem abstractByte_provFragM_bm_eq :
    AbstractByte.provenance_fragM (Provenance := Prov) = AbstractByte.provenance_frag := by
  funext b; cases b <;> rfl

private theorem decodeIntM_bm_eq (it : Gen.IntType) (bs : List Byte) :
    Type.decodeIntM (M := BM) it bs = Type.decodeInt it bs := by
  rcases it with ⟨signed, size⟩
  unfold Type.decodeIntM Type.decodeInt
  rw [abstractByte_dataM_bm_eq]

private theorem encodeIntM_bm_eq (it : Gen.IntType) (v : Val) :
    Type.encodeIntM (M := BM) it v = Type.encodeInt it v := by
  rcases it with ⟨signed, size⟩
  unfold Type.encodeIntM Type.encodeInt
  cases v with
  | Int i => cases Endianness.encode x86_64.ENDIANNESS signed size i <;> rfl
  | _ => rfl

private theorem decodePtrProvenanceM_bm_eq :
    ∀ (idx : Nat) (acc : Option Prov) (bs : List Byte),
      decodePtrProvenanceM (M := BM) idx acc bs = decodePtrProvenance idx acc bs
  | _, _, [] => rfl
  | idx, acc, byte :: rest => by
    unfold decodePtrProvenanceM decodePtrProvenance
    rw [abstractByte_provFragM_bm_eq]
    cases AbstractByte.provenance_frag byte with
    | none => exact decodePtrProvenanceM_bm_eq (idx + 1) none rest
    | some _ => exact decodePtrProvenanceM_bm_eq (idx + 1) _ rest

private theorem firstProvenanceM_bm_eq (bs : List Byte) :
    firstProvenanceM (M := BM) bs = firstProvenance bs := by
  cases bs with
  | nil => rfl
  | cons b _ =>
    unfold firstProvenanceM firstProvenance
    rw [abstractByte_provFragM_bm_eq]
    rfl

private theorem decodePtrM_bm_eq (bs : List Byte) :
    decodePtrM (M := BM) bs = decodePtr bs := by
  unfold decodePtrM decodePtr
  rw [abstractByte_dataM_bm_eq, firstProvenanceM_bm_eq, decodePtrProvenanceM_bm_eq]
  split
  · rfl
  · cases bs.mapM AbstractByte.data <;> rfl

private theorem encodePtrBytesM_bm_eq (prov : Option Prov) :
    ∀ (idx : Nat) (bs : List UInt8),
      encodePtrBytesM (M := BM) prov idx bs = encodePtrBytes prov idx bs
  | _, [] => rfl
  | idx, b :: rest =>
    congrArg
      (Gen.AbstractByte.Init b (prov.map (fun p => { provenance := p, position := (idx : Int) })) :: ·)
      (encodePtrBytesM_bm_eq prov (idx + 1) rest)

private theorem encodePtrM_bm_eq (ptr : Ptr) :
    encodePtrM (M := BM) ptr = encodePtr ptr := by
  unfold encodePtrM encodePtr
  cases Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE ptr.addr with
  | none => rfl
  | some data => dsimp only; rw [encodePtrBytesM_bm_eq]

private theorem decodeWidePtrM_bm_eq (mk : Gen.PointerMetaKind) (bs : List Byte) :
    decodeWidePtrM (M := BM) mk bs = decodeWidePtr mk bs := by
  have hmf : ∀ bs', decodeMetaFieldM (M := BM) mk bs' = decodeMetaField mk bs' := by
    intro bs'
    cases mk with
    | ElementCount => exact decodeIntM_bm_eq IntType.usize_ty bs'
    | VTablePointer _ =>
      unfold decodeMetaFieldM decodeMetaField
      exact bind_congr (decodePtrM_bm_eq bs') (fun optPtr => by cases optPtr <;> rfl)
    | None => rfl
  have hdv : ∀ v, PointerMetaKind.decode_valueM (M := BM) mk v = PointerMetaKind.decode_value mk v := by
    intro v
    cases mk with
    | None =>
      cases v with
      | Tuple vs => cases vs <;> rfl
      | _ => rfl
    | ElementCount => cases v <;> rfl
    | VTablePointer _ =>
      cases v with
      | Ptr p => rcases p with ⟨_, _ | _⟩ <;> rfl
      | _ => rfl
  unfold decodeWidePtrM decodeWidePtr
  split
  · rfl
  · refine bind_congr (decodePtrM_bm_eq _) (fun optThin => ?_)
    cases optThin with
    | none => rfl
    | some _ =>
      dsimp only
      refine bind_congr (hmf _) (fun optMeta => ?_)
      cases optMeta with
      | none => rfl
      | some metaVal =>
        dsimp only
        exact bind_congr (hdv metaVal) (fun pm => by cases pm <;> rfl)

private theorem encodeWidePtrM_bm_eq (mk : Gen.PointerMetaKind) (ptr : Gen.Pointer Prov) :
    encodeWidePtrM (M := BM) mk ptr = encodeWidePtr mk ptr := by
  have hev : PointerMetaKind.encode_as_valueM (M := BM) mk ptr.metadata =
      PointerMetaKind.encode_as_value mk ptr.metadata := by
    cases mk <;> rcases ptr.metadata with _ | (_ | _) <;> rfl
  unfold encodeWidePtrM encodeWidePtr
  refine bind_congr hev (fun metaVal => ?_)
  refine bind_congr (encodePtrM_bm_eq _) (fun _ => ?_)
  dsimp only
  cases mk with
  | ElementCount =>
    exact bind_congr (encodeIntM_bm_eq _ metaVal) (fun _ => rfl)
  | VTablePointer _ =>
    cases metaVal with
    | Ptr p =>
      rcases p with ⟨vp, _ | _⟩
      · exact bind_congr (encodePtrM_bm_eq vp) (fun _ => rfl)
      · rfl
    | _ => rfl
  | None => rfl

namespace PointersMachineInternal

mutual

theorem decodeDiscriminantM_bm_eq {σ : Type}
    (accessor : σ → Gen.Offset → Size → Interp (List Byte × σ)) :
    ∀ (d : Gen.Discriminator) (s : σ),
      decodeDiscriminantM (M := BM) accessor d s = decodeDiscriminant accessor d s
  | .Known _, _ => rfl
  | .Invalid, _ => rfl
  | .Branch offset valueType fallback ⟨children⟩, s => by
    unfold decodeDiscriminantM decodeDiscriminant
    refine bind_congr_right _ (fun ⟨bytes, s1⟩ => ?_)
    dsimp only
    refine bind_congr (decodeIntM_bm_eq valueType bytes) (fun optVal => ?_)
    cases optVal with
    | none => rfl
    | some v =>
      cases v with
      | Int val =>
        have hfb : decodeDiscriminantM (M := BM) accessor fallback =
            decodeDiscriminant accessor fallback := by
          funext s'; exact decodeDiscriminantM_bm_eq accessor fallback s'
        dsimp only
        rw [hfb]
        exact decodeDiscriminantChildrenM_bm_eq accessor val
          (decodeDiscriminant accessor fallback) children s1
      | _ => rfl

theorem decodeDiscriminantChildrenM_bm_eq {σ : Type}
    (accessor : σ → Gen.Offset → Size → Interp (List Byte × σ))
    (val : Int) (onFallback : σ → Interp (Option Int × σ)) :
    ∀ (cs : List ((Int × Int) × Gen.Discriminator)) (s : σ),
      decodeDiscriminantChildrenM (M := BM) accessor val onFallback cs s =
        decodeDiscriminantChildren accessor val onFallback cs s
  | [], _ => rfl
  | ((_, _), child) :: rest, s => by
    unfold decodeDiscriminantChildrenM decodeDiscriminantChildren
    split
    · exact decodeDiscriminantM_bm_eq accessor child s
    · exact decodeDiscriminantChildrenM_bm_eq accessor val onFallback rest s

end

theorem encodeDiscriminantM_bm_eq {σ : Type}
    (accessor : σ → Gen.Offset → List Byte → Interp σ)
    (tagger : Map Gen.Offset (Gen.IntType × Int)) (s : σ) :
    encodeDiscriminantM (M := BM) accessor tagger s = encodeDiscriminant accessor tagger s := by
  have hfn :
      (fun (s' : σ) (entry : Gen.Offset × (Gen.IntType × Int)) => do
        let (offset, (valueType, value)) := entry
        let bytes ← Type.encodeIntM (M := BM) valueType (.Int value)
        accessor s' offset bytes) =
      (fun (s' : σ) (entry : Gen.Offset × (Gen.IntType × Int)) => do
        let (offset, (valueType, value)) := entry
        let bytes ← Type.encodeInt valueType (.Int value)
        accessor s' offset bytes) := by
    funext s' ⟨offset, valueType, value⟩
    exact bind_congr (encodeIntM_bm_eq valueType (.Int value)) (fun _ => rfl)
  unfold encodeDiscriminantM encodeDiscriminant
  rw [hfn]


end PointersMachineInternal

mutual

theorem Type.decodeM_bm_eq :
    ∀ (ty : Gen.«Type») (bs : List Byte),
      Type.decodeM (M := BM) ty bs = Type.decode ty bs
  | .Bool, bs => by
    unfold Type.decodeM Type.decode
    split
    · rfl
    · split <;> split <;> simp_all
  | .Int t, bs => by unfold Type.decodeM Type.decode; exact decodeIntM_bm_eq t bs
  | .Tuple fields headLayout unsizedField, bs => by
    unfold Type.decodeM Type.decode
    cases unsizedField with
    | some _ => rfl
    | none =>
      rcases TupleHeadLayout.head_size_and_align headLayout with ⟨sz, _⟩
      dsimp only
      split
      · rfl
      · exact bind_congr (Type.decodeFieldsM_bm_eq fields bs) (fun o => by cases o <;> rfl)
  | .Array elem count, bs => by
    unfold Type.decodeM Type.decode
    refine bind_congr_right _ (fun _ => ?_)
    refine bind_congr_right _ (fun elemSize => ?_)
    refine bind_congr_right _ (fun _ => ?_)
    split
    · rfl
    · refine bind_congr_right _ (fun chunks => ?_)
      have hfn : (fun elemBytes => Type.decodeM (M := BM) elem elemBytes) =
          (fun elemBytes => Type.decode elem elemBytes) :=
        funext (Type.decodeM_bm_eq elem)
      rw [hfn]
  | .Union _ _ _ _, _ => by
    unfold Type.decodeM Type.decode
    rfl
  | .Enum ⟨variants⟩ _ discriminator _ _, bs => by
    unfold Type.decodeM Type.decode
    split
    · rfl
    · dsimp only
      refine bind_congr (decodeDiscriminantM_bm_eq _ discriminator ()) (fun dp => ?_)
      cases dp.1 with
      | none => rfl
      | some discriminant =>
        dsimp only
        exact bind_congr (Type.decodeVariantM_bm_eq variants discriminant bs) (fun vo => by
          cases vo <;> rfl)
  | .Slice _, _ => by unfold Type.decodeM Type.decode; rfl
  | .TraitObject _, _ => by unfold Type.decodeM Type.decode; rfl
  | .Ptr ptrType, bs => by
    unfold Type.decodeM Type.decode
    cases PtrType.as_wide_pair ptrType with
    | some _ => exact decodeWidePtrM_bm_eq (PtrType.meta_kind ptrType) bs
    | none =>
      dsimp only
      exact bind_congr (decodePtrM_bm_eq bs) (fun po => by cases po <;> rfl)

theorem Type.decodeFieldsM_bm_eq :
    ∀ (fields : List (Gen.Offset × Gen.«Type»)) (bs : List Byte),
      Type.decodeFieldsM (M := BM) fields bs = Type.decodeFields fields bs
  | [], _ => by unfold Type.decodeFieldsM Type.decodeFields; rfl
  | (offset, ty) :: rest, bs => by
    unfold Type.decodeFieldsM Type.decodeFields
    refine bind_congr_right _ (fun _ => ?_)
    refine bind_congr_right _ (fun sz => ?_)
    refine bind_congr_right _ (fun sub => ?_)
    refine bind_congr (Type.decodeM_bm_eq ty sub) (fun vo => ?_)
    cases vo with
    | none => rfl
    | some _ =>
      dsimp only
      exact bind_congr (Type.decodeFieldsM_bm_eq rest bs) (fun vso => by cases vso <;> rfl)

theorem Type.decodeVariantM_bm_eq :
    ∀ (variants : List (Int × Gen.Variant)) (disc : Int) (bs : List Byte),
      Type.decodeVariantM (M := BM) variants disc bs = Type.decodeVariant variants disc bs
  | [], _, _ => by unfold Type.decodeVariantM Type.decodeVariant; rfl
  | (_, ⟨ty, _⟩) :: rest, disc, bs => by
    unfold Type.decodeVariantM Type.decodeVariant
    split
    · exact Type.decodeM_bm_eq ty bs
    · exact Type.decodeVariantM_bm_eq rest disc bs

end

private theorem encodeUnionChunksM_bm_eq :
    ∀ (chunks : List (Gen.Offset × Size)) (chunkData : List (List Byte))
      (bs : List Byte),
      Type.encodeUnionChunksM (M := BM) chunks chunkData bs =
        Type.encodeUnionChunks chunks chunkData bs
  | [], _, _ => rfl
  | (_ :: _), [], _ => rfl
  | (offset, _) :: chunks, data :: chunkData, bs => by
    unfold Type.encodeUnionChunksM Type.encodeUnionChunks
    split
    · rfl
    · exact bind_congr_right _ (fun bs' => encodeUnionChunksM_bm_eq chunks chunkData bs')

mutual

theorem Type.encodeM_bm_eq :
    ∀ (ty : Gen.«Type») (val : Val),
      Type.encodeM (M := BM) ty val = Type.encode ty val
  | .Bool, val => by unfold Type.encodeM Type.encode; cases val <;> rfl
  | .Int t, val => by unfold Type.encodeM Type.encode; exact encodeIntM_bm_eq t val
  | .Tuple fields headLayout unsizedField, val => by
    unfold Type.encodeM Type.encode
    cases unsizedField with
    | some _ => rfl
    | none =>
      rcases TupleHeadLayout.head_size_and_align headLayout with ⟨sz, _⟩
      cases val with
      | Tuple values =>
        dsimp only
        split
        · rfl
        · exact Type.encodeFieldsM_bm_eq fields values _
      | _ => rfl
  | .Array elem _, val => by
    unfold Type.encodeM Type.encode
    cases val with
    | Tuple values =>
      dsimp only
      split
      · rfl
      · have hfn : (fun (value : Val) => do
            let bytes ← Type.encodeM (M := BM) elem value
            let elemLayout ← Type.layout elem
            let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array element is sized"
            if bytes.length ≠ elemSize.bytes then
              specPanic "encode: Type::Array element byte length mismatch"
            else pure bytes) =
          (fun (value : Val) => do
            let bytes ← Type.encode elem value
            let elemLayout ← Type.layout elem
            let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array element is sized"
            if bytes.length ≠ elemSize.bytes then
              specPanic "encode: Type::Array element byte length mismatch"
            else pure bytes) := by
          funext value
          exact bind_congr (Type.encodeM_bm_eq elem value) (fun _ => rfl)
        exact bind_congr (congrArg (fun fn => List.mapM fn values) hfn) (fun _ => rfl)
    | _ => rfl
  | .Union _ chunks _ _, val => by
    unfold Type.encodeM Type.encode
    cases val with
    | Union chunkData =>
      dsimp only
      split
      · rfl
      · exact encodeUnionChunksM_bm_eq chunks chunkData _
    | _ => rfl
  | .Enum ⟨variants⟩ _ _ _ _, val => by
    unfold Type.encodeM Type.encode
    cases val with
    | Variant discriminant data => exact Type.encodeVariantM_bm_eq variants discriminant data
    | _ => rfl
  | .Slice _, _ => by unfold Type.encodeM Type.encode; rfl
  | .TraitObject _, _ => by unfold Type.encodeM Type.encode; rfl
  | .Ptr ptrType, val => by
    unfold Type.encodeM Type.encode
    cases val with
    | Ptr ptr =>
      dsimp only
      cases PtrType.as_wide_pair ptrType with
      | some _ => exact encodeWidePtrM_bm_eq (PtrType.meta_kind ptrType) ptr
      | none =>
        rcases ptr with ⟨tp, _ | _⟩
        · exact encodePtrM_bm_eq tp
        · rfl
    | _ => rfl

theorem Type.encodeFieldsM_bm_eq :
    ∀ (fields : List (Gen.Offset × Gen.«Type»)) (values : List Val)
      (bs : List Byte),
      Type.encodeFieldsM (M := BM) fields values bs = Type.encodeFields fields values bs
  | [], _, _ => by unfold Type.encodeFieldsM Type.encodeFields; rfl
  | (_ :: _), [], _ => by unfold Type.encodeFieldsM Type.encodeFields; rfl
  | (offset, ty) :: fields, value :: values, bs => by
    unfold Type.encodeFieldsM Type.encodeFields
    refine bind_congr (Type.encodeM_bm_eq ty value) (fun fbs => ?_)
    exact bind_congr_right _ (fun bs' => Type.encodeFieldsM_bm_eq fields values bs')

theorem Type.encodeVariantM_bm_eq :
    ∀ (variants : List (Int × Gen.Variant)) (disc : Int) (data : Val),
      Type.encodeVariantM (M := BM) variants disc data = Type.encodeVariant variants disc data
  | [], _, _ => by unfold Type.encodeVariantM Type.encodeVariant; rfl
  | (_, ⟨ty, tagger⟩) :: rest, disc, data => by
    unfold Type.encodeVariantM Type.encodeVariant
    split
    · exact bind_congr (Type.encodeM_bm_eq ty data) (fun bs =>
        encodeDiscriminantM_bm_eq _ tagger bs)
    · exact Type.encodeVariantM_bm_eq rest disc data

end

private theorem checkUnionChunksM_bm_eq :
    ∀ (chunkData : List (List Byte)) (chunks : List (Gen.Offset × Size)),
      checkUnionChunksM chunkData chunks = checkUnionChunks chunkData chunks
  | [], _ => rfl
  | (_ :: _), [] => rfl
  | data :: chunkData, (_, _) :: chunks => by
    unfold checkUnionChunksM checkUnionChunks
    exact bind_congr_right _ (fun _ => checkUnionChunksM_bm_eq chunkData chunks)

private theorem vtableLookupM_bm_eq (m : Mach) :
    vtableLookupM (M := BM) m = vtableLookup m := by
  funext (ptr : Ptr)
  unfold vtableLookupM vtableLookup
  conv =>
    lhs
    rw [find?_eq_of_eq (q := fun e : Gen.VTableName × Ptr => decide (e.2 = ptr))
      (by intro ⟨_, vp⟩; exact congrArg (@decide (vp = ptr)) (Subsingleton.elim _ _))]
  conv =>
    rhs
    rw [find?_eq_of_eq (q := fun e : Gen.VTableName × Ptr => decide (e.2 = ptr))
      (by intro ⟨_, vp⟩; rfl)]
  rcases m.vtable_ptrs.entries.find? (fun e : Gen.VTableName × Ptr => decide (e.2 = ptr)) with
    _ | ⟨_, _⟩ <;> rfl

/-- The polymorphic `Machine::vtable_from_ptr` at `M = BasicMemory<x86_64>` is
`vtableFromPtr`. -/
theorem vtableFromPtrM_bm_eq (m : Mach) :
    vtableFromPtrM (M := BM) m = vtableFromPtr m := by
  funext (ptr : Ptr)
  unfold vtableFromPtrM vtableFromPtr
  conv =>
    lhs
    rw [find?_eq_of_eq (q := fun e : Gen.VTableName × Ptr => decide (e.2 = ptr))
      (by intro ⟨_, vp⟩; exact congrArg (@decide (vp = ptr)) (Subsingleton.elim _ _))]
  conv =>
    rhs
    rw [find?_eq_of_eq (q := fun e : Gen.VTableName × Ptr => decide (e.2 = ptr))
      (by intro ⟨_, vp⟩; rfl)]
  rcases m.vtable_ptrs.entries.find? (fun e : Gen.VTableName × Ptr => decide (e.2 = ptr)) with
    _ | ⟨_, _⟩ <;> rfl

private theorem checkPtrMetadataM_bm_eq (pm : Option (Gen.PointerMeta Prov))
    (kind : Gen.PointerMetaKind) (m : Option Mach) :
    checkPtrMetadataM pm kind (m.map (vtableFromPtrM (M := BM) ·)) =
      checkPtrMetadata pm kind m := by
  unfold checkPtrMetadataM checkPtrMetadata
  rcases pm with _ | (_ | _) <;> cases kind <;> try rfl
  cases m with
  | none => rfl
  | some mach => dsimp only [Option.map]; rw [vtableFromPtrM_bm_eq]

namespace PointersMachineInternal

theorem cm_dereferenceable_bm_eq (cm : Gen.ConcurrentMemory BM) (ptr : Ptr) (sz : Size) :
    ConcurrentMemory.dereferenceable (M := BM) cm ptr sz =
      CM.dereferenceable cm ptr sz := rfl

end PointersMachineInternal

private theorem checkPtrM_bm_eq (ptr : Gen.Pointer Prov) (ptrTy : Gen.PtrType)
    (m : Option Mach) :
    checkPtrM (M := BM) ptr ptrTy m = checkPtr ptr ptrTy m := by
  unfold checkPtrM checkPtr
  refine bind_congr_right _ (fun _ => ?_)
  refine bind_congr (checkPtrMetadataM_bm_eq _ _ _) (fun _ => ?_)
  cases PtrType.safe_pointee ptrTy with
  | none =>
    cases ptrTy with
    | VTablePtr _ =>
      cases m with
      | none => rfl
      | some mach => dsimp only; rw [vtableFromPtrM_bm_eq]
    | _ => rfl
  | some pointee =>
    dsimp only
    refine bind_congr ?_ (fun ⟨size, align⟩ => ?_)
    · cases m with
      | none => rfl
      | some mach => dsimp only; rw [vtableLookupM_bm_eq]
    · dsimp only
      refine bind_congr_right _ (fun _ => ?_)
      refine bind_congr_right _ (fun _ => ?_)
      refine bind_congr_right _ (fun _ => ?_)
      refine bind_congr_right _ (fun _ => ?_)
      cases m with
      | none =>
        dsimp only
        split
        · rfl
        · cases ptr.thin_pointer.provenance <;> rfl
      | some mach =>
        dsimp only [cm_dereferenceable_bm_eq]

mutual

theorem checkValueM_bm_eq :
    ∀ (val : Val) (ty : Gen.«Type») (m : Option Mach),
      checkValueM (M := BM) val ty m = checkValue val ty m
  | val, .Int _, _ => by unfold checkValueM checkValue; cases val <;> rfl
  | val, .Bool, _ => by unfold checkValueM checkValue; cases val <;> rfl
  | val, .Ptr ptrTy, m => by
    unfold checkValueM checkValue
    cases val with
    | Ptr ptr => exact checkPtrM_bm_eq ptr ptrTy m
    | _ => rfl
  | val, .Tuple fields _ unsizedField, m => by
    unfold checkValueM checkValue
    cases val with
    | Tuple vals =>
      cases unsizedField with
      | some _ => rfl
      | none =>
        dsimp only
        exact bind_congr_right _ (fun _ => checkFieldsM_bm_eq vals fields m)
    | _ => rfl
  | val, .Array elem count, m => by
    unfold checkValueM checkValue
    cases val with
    | Tuple vals =>
      dsimp only
      refine bind_congr_right _ (fun _ => ?_)
      have hfn : (fun (v : Val) => checkValueM (M := BM) v elem m) =
          (fun (v : Val) => checkValue v elem m) :=
        funext (fun v => checkValueM_bm_eq v elem m)
      rw [hfn]
    | _ => rfl
  | val, .Union _ chunks _ _, _ => by
    unfold checkValueM checkValue
    cases val with
    | Union chunkData =>
      dsimp only
      exact bind_congr_right _ (fun _ => checkUnionChunksM_bm_eq chunkData chunks)
    | _ => rfl
  | val, .Enum ⟨variants⟩ _ _ _ _, m => by
    unfold checkValueM checkValue
    cases val with
    | Variant disc data => exact checkVariantM_bm_eq variants disc data m
    | _ => rfl
  | val, .Slice _, _ => by unfold checkValueM checkValue; cases val <;> rfl
  | val, .TraitObject _, _ => by unfold checkValueM checkValue; cases val <;> rfl

theorem checkFieldsM_bm_eq :
    ∀ (vals : List Val) (fields : List (Gen.Offset × Gen.«Type»)) (m : Option Mach),
      checkFieldsM (M := BM) vals fields m = checkFields vals fields m
  | [], _, _ => by unfold checkFieldsM checkFields; rfl
  | (_ :: _), [], _ => by unfold checkFieldsM checkFields; rfl
  | val :: vals, (_, ty) :: fields, m => by
    unfold checkFieldsM checkFields
    exact bind_congr (checkValueM_bm_eq val ty m) (fun _ => checkFieldsM_bm_eq vals fields m)

theorem checkVariantM_bm_eq :
    ∀ (variants : List (Int × Gen.Variant)) (disc : Int) (data : Val) (m : Option Mach),
      checkVariantM (M := BM) variants disc data m = checkVariant variants disc data m
  | [], _, _, _ => by unfold checkVariantM checkVariant; rfl
  | (_, ⟨ty, _⟩) :: rest, disc, data, m => by
    unfold checkVariantM checkVariant
    split
    · exact checkValueM_bm_eq data ty m
    · exact checkVariantM_bm_eq rest disc data m

end

namespace PointersMachineInternal

theorem cm_load_bm_eq (cm : Gen.ConcurrentMemory BM) (ptr : Ptr) (len : Size)
    (align : Align) (atomicity : Gen.Atomicity) :
    ConcurrentMemory.load (M := BM) cm ptr len align atomicity =
      CM.load cm ptr len align atomicity := rfl

theorem cm_store_bm_eq (cm : Gen.ConcurrentMemory BM) (ptr : Ptr) (bs : List Byte)
    (align : Align) (atomicity : Gen.Atomicity) :
    ConcurrentMemory.store (M := BM) cm ptr bs align atomicity =
      CM.store cm ptr bs align atomicity := rfl

theorem cm_deinit_bm_eq (cm : Gen.ConcurrentMemory BM) (ptr : Ptr) (len : Size)
    (align : Align) :
    ConcurrentMemory.deinit (M := BM) cm ptr len align =
      CM.deinit cm ptr len align := rfl

theorem cm_signed_deref_bm_eq (cm : Gen.ConcurrentMemory BM) (ptr : Ptr) (off : Int) :
    ConcurrentMemory.signed_dereferenceable (M := BM) cm ptr off =
      CM.signed_dereferenceable cm ptr off := rfl

theorem cm_allocate_bm_eq (cm : Gen.ConcurrentMemory BM) (kind : Gen.AllocationKind)
    (size : Size) (align : Align) :
    ConcurrentMemory.allocate (M := BM) cm kind size align =
      CM.allocate cm kind size align := by
  unfold ConcurrentMemory.allocate CM.allocate MemoryOps.allocate instMemoryOpsBM
  rfl

theorem cm_deallocate_bm_eq (cm : Gen.ConcurrentMemory BM) (ptr : Ptr)
    (kind : Gen.AllocationKind) (size : Size) (align : Align) :
    ConcurrentMemory.deallocate (M := BM) cm ptr kind size align =
      CM.deallocate cm ptr kind size align := rfl

theorem cm_check_data_races_bm_eq (cm : Gen.ConcurrentMemory BM) (tid : Gen.ThreadId)
    (prev : Set Gen.ThreadId × List Gen.Access) :
    ConcurrentMemory.check_data_races (M := BM) cm tid prev =
      CM.check_data_races cm tid prev := rfl

theorem storageDeadM_bm_eq (fr : Frame) (cm : Gen.ConcurrentMemory BM)
    (l : Gen.LocalName) :
    storageDeadM (M := BM) fr cm l = storageDead fr cm l := by
  unfold storageDeadM storageDead
  refine bind_congr_right _ (fun _ => ?_)
  refine bind_congr_right _ (fun _ => ?_)
  refine bind_congr_right _ (fun sz => ?_)
  refine bind_congr_right _ (fun al => ?_)
  rcases mapRemove fr.locals l with ⟨_ | ptr, _⟩
  · rfl
  · exact bind_congr (cm_deallocate_bm_eq cm ptr .Stack sz al) (fun _ => rfl)

theorem storageLiveM_bm_eq (fr : Frame) (cm : Gen.ConcurrentMemory BM)
    (l : Gen.LocalName) :
    storageLiveM (M := BM) fr cm l = storageLive fr cm l := by
  unfold storageLiveM storageLive
  refine bind_congr (storageDeadM_bm_eq fr cm l) (fun ⟨fr2, cm2⟩ => ?_)
  dsimp only
  refine bind_congr_right _ (fun _ => ?_)
  refine bind_congr_right _ (fun _ => ?_)
  refine bind_congr_right _ (fun sz => ?_)
  refine bind_congr_right _ (fun al => ?_)
  exact bind_congr (cm_allocate_bm_eq cm2 .Stack sz al) (fun ⟨_, _⟩ => rfl)

theorem computeSizeM_bm_eq (m : Mach) (layout : Gen.LayoutStrategy)
    (pm : Option (Gen.PointerMeta Prov)) :
    computeSizeM (M := BM) m layout pm = computeSize m layout pm := by
  unfold computeSizeM computeSize
  rw [vtableLookupM_bm_eq]

theorem computeAlignM_bm_eq (m : Mach) (layout : Gen.LayoutStrategy)
    (pm : Option (Gen.PointerMeta Prov)) :
    computeAlignM (M := BM) m layout pm = computeAlign m layout pm := by
  unfold computeAlignM computeAlign
  rw [vtableLookupM_bm_eq]

theorem typedLoadM_bm_eq (m : Mach) (ptr : Ptr) (ty : Gen.«Type») (align : Align)
    (atomicity : Gen.Atomicity) :
    typedLoadM (M := BM) m ptr ty align atomicity = typedLoad m ptr ty align atomicity := by
  unfold typedLoadM typedLoad
  refine bind_congr_right _ (fun _ => ?_)
  refine bind_congr_right _ (fun sz => ?_)
  refine bind_congr (cm_load_bm_eq m.mem ptr sz align atomicity) (fun ⟨bs, cm⟩ => ?_)
  dsimp only
  refine bind_congr (Type.decodeM_bm_eq ty bs) (fun optVal => ?_)
  cases optVal with
  | none => rfl
  | some val =>
    dsimp only
    exact bind_congr (checkValueM_bm_eq val ty (some { m with mem := cm })) (fun _ => rfl)

theorem typedStoreM_bm_eq (m : Mach) (ptr : Ptr) (val : Val) (ty : Gen.«Type»)
    (align : Align) (atomicity : Gen.Atomicity) :
    typedStoreM (M := BM) m ptr val ty align atomicity = typedStore m ptr val ty align atomicity := by
  unfold typedStoreM typedStore
  dsimp only
  rw [checkValueM_bm_eq]
  cases checkValue val ty (some m) with
  | error _ => rfl
  | ok _ =>
    dsimp only
    refine bind_congr (Type.encodeM_bm_eq ty val) (fun bs => ?_)
    exact bind_congr (cm_store_bm_eq m.mem ptr bs align atomicity) (fun _ => rfl)

theorem placeLoadM_bm_eq (m : Mach) (place : Gen.Place BM) (ty : Gen.«Type») :
    placeLoadM (M := BM) m place ty = placeLoad m place ty := by
  unfold placeLoadM placeLoad
  rw [typedLoadM_bm_eq]

theorem placeStoreM_bm_eq (m : Mach) (place : Gen.Place BM) (val : Val) (ty : Gen.«Type») :
    placeStoreM (M := BM) m place val ty = placeStore m place val ty := by
  unfold placeStoreM placeStore
  rw [typedStoreM_bm_eq]

end PointersMachineInternal

private theorem transmuteM_bm_eq (val : Val) (t1 t2 : Gen.«Type») (m : Option Mach) :
    transmuteM (M := BM) val t1 t2 m = transmute val t1 t2 m := by
  unfold transmuteM transmute
  refine bind_congr_right _ (fun _ => ?_)
  refine bind_congr_right _ (fun _ => ?_)
  refine bind_congr_right _ (fun _ => ?_)
  refine bind_congr_right _ (fun _ => ?_)
  split
  · rfl
  · refine bind_congr (Type.encodeM_bm_eq t1 val) (fun bs => ?_)
    refine bind_congr (Type.decodeM_bm_eq t2 bs) (fun optV => ?_)
    cases optV with
    | none => rfl
    | some rawVal =>
      dsimp only
      exact bind_congr (checkValueM_bm_eq rawVal t2 m) (fun _ => rfl)

private theorem evalCastOpM_bm_eq (cop : Gen.CastOp) (arg : Val × Gen.«Type») (m : Option Mach) :
    evalCastOpM (M := BM) cop arg m = evalCastOp cop arg m := by
  rcases arg with ⟨v, oldTy⟩
  cases cop with
  | IntToInt _ => unfold evalCastOpM evalCastOp; cases v <;> rfl
  | Transmute newTy =>
    unfold evalCastOpM evalCastOp
    dsimp only
    refine bind_congr_right _ (fun _ => ?_)
    refine bind_congr_right _ (fun _ => ?_)
    refine bind_congr_right _ (fun _ => ?_)
    refine bind_congr_right _ (fun _ => ?_)
    split
    · rfl
    · exact bind_congr (transmuteM_bm_eq v oldTy newTy m) (fun _ => rfl)

namespace PointersMachineInternal

theorem evalUnOpM_bm_eq (op : Gen.UnOp) (arg : Val × Gen.«Type») (m : Option Mach) :
    evalUnOpM (M := BM) op arg m = evalUnOp op arg m := by
  rcases arg with ⟨v, ty⟩
  unfold evalUnOpM evalUnOp
  cases op with
  | Int iop =>
    cases v with
    | Int operand =>
      cases ty with
      | Int intTy =>
        dsimp only
        refine bind_congr_right _ (fun r => ?_)
        cases iop <;> (dsimp only; rw [checkValueM_bm_eq])
      | _ => rfl
    | _ => rfl
  | Cast cop => exact evalCastOpM_bm_eq cop (v, ty) m
  | GetThinPointer =>
    cases v with
    | Ptr p => rcases p with ⟨_, _⟩; rfl
    | _ => rfl
  | GetMetadata =>
    cases v with
    | Ptr ptr =>
      cases ty with
      | Ptr ptrTy =>
        have hev : PointerMetaKind.encode_as_valueM (M := BM) (PtrType.meta_kind ptrTy) ptr.metadata =
            PointerMetaKind.encode_as_value (PtrType.meta_kind ptrTy) ptr.metadata := by
          cases PtrType.meta_kind ptrTy <;> rcases ptr.metadata with _ | (_ | _) <;> rfl
        dsimp only
        rw [hev]
        refine bind_congr_right _ (fun mv => ?_)
        cases PtrType.meta_kind ptrTy with
        | VTablePointer _ =>
          cases m with
          | none => rfl
          | some mach => dsimp only; rw [checkValueM_bm_eq]
        | _ => dsimp only; rw [checkValueM_bm_eq]
      | _ => rfl
    | _ => rfl
  | ComputeSize cty =>
    have hdv : PointerMetaKind.decode_valueM (M := BM) (Type.meta_kind cty) v =
        PointerMetaKind.decode_value (Type.meta_kind cty) v := by
      cases Type.meta_kind cty <;> cases v <;>
        first
        | rfl
        | (rename_i xs; cases xs <;> rfl)
        | (rename_i p; rcases p with ⟨_, _ | _⟩ <;> rfl)
    dsimp only
    rw [hdv]
    refine bind_congr_right _ (fun pm => ?_)
    refine bind_congr_right _ (fun lay => ?_)
    cases m with
    | none => rfl
    | some mach => dsimp only; rw [computeSizeM_bm_eq]
  | ComputeAlign cty =>
    have hdv : PointerMetaKind.decode_valueM (M := BM) (Type.meta_kind cty) v =
        PointerMetaKind.decode_value (Type.meta_kind cty) v := by
      cases Type.meta_kind cty <;> cases v <;>
        first
        | rfl
        | (rename_i xs; cases xs <;> rfl)
        | (rename_i p; rcases p with ⟨_, _ | _⟩ <;> rfl)
    dsimp only
    rw [hdv]
    refine bind_congr_right _ (fun pm => ?_)
    refine bind_congr_right _ (fun lay => ?_)
    cases m with
    | none => rfl
    | some mach => dsimp only; rw [computeAlignM_bm_eq]
  | VTableMethodLookup _ =>
    cases v with
    | Ptr ptr =>
      cases ty with
      | Ptr _ =>
        cases m with
        | none => rfl
        | some mach => dsimp only; rw [vtableLookupM_bm_eq]
      | _ => rfl
    | _ => rfl

end PointersMachineInternal

end MiniRustSpec.Correspondence
