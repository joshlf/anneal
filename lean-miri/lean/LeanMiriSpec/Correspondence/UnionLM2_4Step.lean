/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.UnionLM2_4Core

/-!
# Union Allocations (Continued) and State Relation (`LM-2.4`)

Continuation of `LeanMiriSpec.Correspondence.UnionLM2_4Core`, containing the
union allocation copy/prefix-mask lemmas (Section 8 continued) and the `LM-2.4`
state/step relations (`UnionMemRel`, `UnionLocalRel`, `FrameRelLM2_4`,
`StateRelLM2_4`, `StepRelLM2_4`, Section 9).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-- Overwriting `[0, finish)` on any `InitMask` with `len.bytes ≤ finish.bytes`
takes `InitMask.setRange`'s `fullOverwrite` fast path in both `.Lazy` and
`.Materialized` representations, returning `⟨.Lazy newState, finish⟩`. -/
theorem initMask_setRange_full_overwrite (mask : Miri.Memory.InitMask)
    (range : Miri.Memory.AllocRange) (finish : Miri.ABI.Size) (newState : Bool)
    (hend : range.endExclusive = .ok finish)
    (hstart : range.start.bytes = 0)
    (hlen : mask.len.bytes ≤ finish.bytes) :
    mask.setRange range newState = .ok ⟨.Lazy newState, finish⟩ := by
  cases mask with
  | mk blocks len =>
    cases blocks <;>
      simp [Miri.Memory.InitMask.setRange, hend, hstart, hlen,
        Pure.pure, Except.pure, Bind.bind, Except.bind]

/-- Every `IsUnionPrefixMask S k` has `len = translateSizeBytes S`. -/
theorem IsUnionPrefixMask.len_eq {S k : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) : M.len = translateSizeBytes S := by
  rcases hM with rfl | rfl
  · unfold unionPrefixMask
    split <;> rfl
  · unfold unionCopiedPrefixMask
    split <;> rfl

/-- Writing `[0, k')` (`k' ≤ k ≤ S`) onto `IsUnionPrefixMask S k M` leaves the
initialized prefix `[0, k)` intact (`IsUnionPrefixMask S k M'`). -/
theorem IsUnionPrefixMask.setRange_le {S k k' : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hk' : ValidScalarBytes k') (hk'k : k' ≤ k) (hkS : k ≤ S) :
    ∃ M', M.setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes k')) true = .ok M' ∧
      IsUnionPrefixMask S k M' := by
  rcases hM with rfl | rfl
  · refine ⟨unionPrefixMask S k, ?_, .of_fresh S k⟩
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
      first | omega | with_unfolding_all decide
  · refine ⟨unionCopiedPrefixMask S k, ?_, .of_copied S k⟩
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
      first | omega | with_unfolding_all decide

/-- Writing `[0, k')` onto `IsUnionPrefixMask S k M` yields a mask initializing
`[0, max k k')` (`IsUnionPrefixMask S (max k k') M'`). -/
theorem IsUnionPrefixMask.setRange_max {S k k' : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hk' : ValidScalarBytes k') (hkS : k ≤ S) (hk'S : k' ≤ S) :
    ∃ M', M.setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes k')) true = .ok M' ∧
      IsUnionPrefixMask S (max k k') M' := by
  rcases Nat.le_total k k' with hle | hge
  · rw [Nat.max_eq_right hle]
    exact hM.setRange_ge hS hk hk' hle hk'S
  · rw [Nat.max_eq_left hge]
    exact hM.setRange_le hS hk hk' hge hkS

/-- Writing a `k`-byte scalar at offset `0` of an `S`-byte allocation (`k ≤ S`)
stores `allocLeBytes sc.bits k` in `[0, k)` AND preserves the trailing raw bytes
`[k, S)` unchanged. -/
theorem union_writeScalar_prefix_preserve_high
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) {E : Type} {A : Miri.Memory.Allocation AnnealProv E} {S : Nat}
    (hlen : A.len = S) (hsz : A.byteSize = translateSizeBytes S) (hS : S ≤ 16)
    (hle : sc.sizeBytes ≤ S)
    (hmut : A.mutability = .Mut) (hprov : A.provenanceMap = Miri.Memory.ProvenanceMap.new)
    {M' : Miri.Memory.InitMask}
    (hset : A.initializationMask.setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) true =
        .ok M') :
    ∃ A' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO msc.size)
        (Miri.Memory.Scalar.fromScalarInt msc) A = .ok () A' ∧
      A'.byteSize = A.byteSize ∧
      A'.len = S ∧
      A'.align = A.align ∧
      A'.mutability = .Mut ∧
      A'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      A'.initializationMask = M' ∧
      A'.extra = A.extra ∧
      A'.nativeBuffer = A.nativeBuffer ∧
      (unionAllocRaw A').extract 0 sc.sizeBytes = allocLeBytes sc.bits sc.sizeBytes ∧
      (unionAllocRaw A').extract sc.sizeBytes S = (unionAllocRaw A).extract sc.sizeBytes S := by
  have hn := translateSizeBytes_toNat_of_valid hrel.validBytes
  have hn16 := translateSizeBytes_le_16_of_valid hrel.validBytes
  have hlt : Miri.ABI.Size.ZERO.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat <
      2 ^ 64 := by
    rw [hn]; simp [Miri.ABI.Size.ZERO]; omega
  have hend := allocRange_endExclusive_of_lt hlt
  have hrange :
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)).size =
        translateSizeBytes sc.sizeBytes := rfl
  have hconv := u_toBitsOrPtrInternal hrel
  have hslice : Miri.Memory.Allocation.getBytesUnchecked A
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) =
      .ok ((unionAllocRaw A).extract 0 sc.sizeBytes) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen hsz hS hle]
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice
  unfold Miri.Memory.Allocation.initializationMask at hset
  have hprov2 := hprov
  unfold Miri.Memory.Allocation.provenanceMap at hprov2
  rw [hrel.size_eq]
  unfold Miri.Memory.Allocation.writeScalar
  simp only [hmut, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hrange, hconv, pure_bind]
  rw [hslice]
  simp only [hset]
  rw [hprov2, Miri.Memory.ProvenanceMap.clear_new _ _ _ _ ?pos hend]
  case pos => decide
  simp only []
  split
  · rename_i data hdata
    have hdata' : uTargetUIntBytes annealTargetDataLayout
        (translateSizeBytes sc.sizeBytes) (BitVec.ofNat 128 sc.bits) = .ok data := hdata
    rw [uTargetUIntBytes_spec _ _ hn16] at hdata'
    cases hdata'
    have hstart : (Miri.Memory.allocRange Miri.ABI.Size.ZERO
        (translateSizeBytes sc.sizeBytes)).start.bytes.toNat = 0 := rfl
    have htoNat : (BitVec.ofNat 128 sc.bits).toNat = sc.bits :=
      bitVec_ofNat_128_toNat hrel.validBytes hrel.canonical
    have hSn : (translateSizeBytes S).bytes.toNat = S := by
      simp only [translateSizeBytes, Miri.ABI.Size.ofBytes, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    have hlen' := hlen
    unfold Miri.Memory.Allocation.len at hlen'
    have hsz' := hsz
    unfold Miri.Memory.Allocation.byteSize at hsz'
    have hbytes_size :
        ((unionAllocRaw A).extract 0 0 ++ allocLeBytes sc.bits sc.sizeBytes ++
          (unionAllocRaw A).extract sc.sizeBytes (unionAllocRaw A).size).size = S := by
      have hr : (unionAllocRaw A).size = S := hlen
      simp only [Array.size_append, Array.size_extract, allocLeBytes_size, hr]
      omega
    have hbytes_size' :
        ((unionAllocRaw A).extract 0
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO
              (translateSizeBytes sc.sizeBytes)).start.bytes.toNat ++
          allocLeBytes (BitVec.ofNat 128 sc.bits).toNat
            (translateSizeBytes sc.sizeBytes).bytes.toNat ++
          (unionAllocRaw A).extract
            ((Miri.Memory.allocRange Miri.ABI.Size.ZERO
              (translateSizeBytes sc.sizeBytes)).start.bytes.toNat +
              (translateSizeBytes sc.sizeBytes).bytes.toNat)
            (unionAllocRaw A).size).size =
          A.byteSize.bytes.toNat := by
      rw [hsz, hSn]
      simpa only [hstart, htoNat, hn, Nat.zero_add] using hbytes_size
    unfold unionAllocRaw at hbytes_size'
    unfold Miri.Memory.Allocation.byteSize at hbytes_size'
    simp only [hbytes_size', bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · show (_ : Array UInt8).size = S
      have := hbytes_size'
      rw [hsz', hSn] at this
      exact this
    · show ((Miri.Memory.Allocation.casesOn (motive := fun _ => Array UInt8) A
          (fun raw _ _ _ _ _ _ _ => raw)).extract 0 0 ++ _ ++ _).extract 0 sc.sizeBytes = _
      simp only [hstart, htoNat, hn, Nat.zero_add]
      rw [Array.extract_append, Array.extract_append]
      simp [allocLeBytes_size]
    · show ((unionAllocRaw A).extract 0 _ ++ _ ++
          (unionAllocRaw A).extract _ (unionAllocRaw A).size).extract sc.sizeBytes S = _
      simp only [hstart, htoNat, hn, Nat.zero_add]
      have hr : (unionAllocRaw A).size = S := hlen
      rw [hr, Array.extract_empty_of_stop_le_start (Nat.le_refl 0), Array.empty_append,
        Array.extract_append, Array.extract_eq_empty_of_le (by simp [allocLeBytes_size]; omega),
        Array.empty_append]
      simp only [allocLeBytes_size, Nat.sub_self, Array.extract_extract, Nat.add_zero,
        Nat.min_eq_right (by omega : S ≤ sc.sizeBytes + (S - sc.sizeBytes))]
  · rename_i err herr
    have herr' : uTargetUIntBytes annealTargetDataLayout
        (translateSizeBytes sc.sizeBytes) (BitVec.ofNat 128 sc.bits) = .error err := herr
    rw [uTargetUIntBytes_spec _ _ hn16] at herr'
    cases herr'

set_option maxHeartbeats 800000 in
/-- Running `Miri.Memory.Allocation.copy` (`copyRepeatedly ... 1 ...`) from an
`S`-byte union allocation `src` (`IsUnionPrefixMask S k`) into **any** distinct
mutable `S`-byte destination allocation `dest` (regardless of `dest`'s prior raw
bytes or initialization mask, so long as `dest.initializationMask.len =
translateSizeBytes S`) overwrites `dest` completely with `src`'s raw bytes and
`unionCopiedPrefixMask S k` (`IsUnionPrefixMask S k`). -/
theorem union_copy_alloc_spec {E : Type}
    {src dest : Miri.Memory.Allocation AnnealProv E} {S k : Nat}
    (hS : ValidScalarBytes S) (hk : ValidScalarBytes k) (hle : k ≤ S)
    (hlen_src : src.len = S) (hsz_src : src.byteSize = translateSizeBytes S)
    (hprov_src : src.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_src : IsUnionPrefixMask S k src.initializationMask)
    (hlen_dst : dest.len = S)
    (hsz_dst : dest.byteSize = translateSizeBytes S)
    (hmut_dst : dest.mutability = .Mut)
    (hprov_dst : dest.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_dst : dest.initializationMask.len = translateSizeBytes S) :
    ∃ dest' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copy src
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true dest = .ok () dest' ∧
      dest'.byteSize = translateSizeBytes S ∧
      dest'.len = S ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = unionCopiedPrefixMask S k ∧
      IsUnionPrefixMask S k dest'.initializationMask ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      unionAllocRaw dest' = unionAllocRaw src := by
  have hS16 : S ≤ 16 := by rcases hS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hSn : (translateSizeBytes S).bytes.toNat = S := by
    simp only [translateSizeBytes, Miri.ABI.Size.ofBytes, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hend : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).endExclusive =
      .ok (translateSizeBytes S) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hnz_sz : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size.bytes ==
      0) = false := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hslice_src : Miri.Memory.Allocation.getBytesUnchecked src
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok ((unionAllocRaw src).extract 0 S) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen_src hsz_src hS16 (Nat.le_refl S)]
  have hslice_dst : Miri.Memory.Allocation.getBytesUnchecked dest
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok ((unionAllocRaw dest).extract 0 S) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen_dst hsz_dst hS16 (Nat.le_refl S)]
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice_src hslice_dst
  have hprep_prov := provenanceMap_prepareCopy_new hS (unionAllocRaw src)
  unfold unionAllocRaw at hprep_prov
  have hno_uninit := unionInitCopy_noBytesInit hS hk hle
  have hmul : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size.mul 1 =
      .ok (translateSizeBytes S) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hloop (b : Array UInt8) :
      forIn [: (1 : UInt64).toNat] (#[] : Array UInt8) (fun _ r =>
        (pure (ForInStep.yield (r ++ b)) : Id (ForInStep (Array UInt8)))) = b := by
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
    rfl
  induction src using Miri.Memory.Allocation.casesOn
  rename_i srcRaw srcSz srcProv srcMask srcAlign srcMut srcExtra srcNat
  induction dest using Miri.Memory.Allocation.casesOn
  rename_i destRaw destSz destProv destMask destAlign destMut destExtra destNat
  change srcRaw.size = S at hlen_src
  change srcSz = translateSizeBytes S at hsz_src
  change srcProv = Miri.Memory.ProvenanceMap.new at hprov_src
  change IsUnionPrefixMask S k srcMask at hmask_src
  have hprep_mask := isUnionPrefixMask_prepareCopy hS hk hle hmask_src
  change destRaw.size = S at hlen_dst
  change destSz = translateSizeBytes S at hsz_dst
  change destMut = .Mut at hmut_dst
  change destProv = Miri.Memory.ProvenanceMap.new at hprov_dst
  change destMask.len = translateSizeBytes S at hmask_dst
  change _ = Except.ok (srcRaw.extract 0 S) at hslice_src
  change _ = Except.ok (destRaw.extract 0 S) at hslice_dst
  change (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
      srcRaw (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ at hprep_prov
  subst hsz_src hprov_src hsz_dst hmut_dst hprov_dst
  have hsrc_ext : srcRaw.extract 0 S = srcRaw := by
    rw [← hlen_src]
    exact Array.extract_eq_self_of_le (Nat.le_refl _)
  rw [hsrc_ext] at hslice_src
  have hset_dst : destMask.setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) true =
      .ok ⟨.Lazy true, translateSizeBytes S⟩ :=
    initMask_setRange_full_overwrite destMask
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
      (translateSizeBytes S) true hend rfl (by rw [hmask_dst]; exact UInt64.le_refl _)
  have hclr_dst := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) destRaw
    (Miri.ABI.Size.ofBytes 8) (translateSizeBytes S) (by decide) hend
  unfold Miri.Memory.Allocation.copy Miri.Memory.Allocation.copyRepeatedly
  simp only [hloop]
  rw [hslice_src]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [hmul]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hslice_dst]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_prov]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_mask]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  simp only [hno_uninit, show ((1 : UInt64) == 0) = false from rfl,
    show (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size =
      translateSizeBytes S from rfl,
    provenanceMap_applyCopy_empty, Bool.not_true, Bool.false_and, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i _ updated₁ hprep_ovw
    have hu1 : allocResultTuple (.ok () updated₁) =
        some (destRaw, translateSizeBytes S, Miri.Memory.ProvenanceMap.new,
          ⟨.Lazy true, translateSizeBytes S⟩, destAlign, .Mut, destExtra, destNat) := by
      have hpo := hprep_ovw
      with_unfolding_all
        conv at hpo => lhs; whnf
        rw [hslice_dst] at hpo
        dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
        simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
        conv at hpo => lhs; arg 2; whnf
        simp only [hset_dst, Except.mapError] at hpo
        dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
        rw [hclr_dst] at hpo
        cases hpo
        rfl
    split
    · rename_i _ updated₂ hovw
      have hu2 : allocExceptTuple (.ok updated₂) =
          some (srcRaw, translateSizeBytes S, Miri.Memory.ProvenanceMap.new,
            ⟨.Lazy true, translateSizeBytes S⟩, destAlign, .Mut, destExtra, destNat) := by
        have hovw2 : ∃ (k_fn : Miri.ABI.Size → Except Miri.Memory.AllocError
            (Miri.Memory.Allocation AnnealProv E)),
            (∀ finish, allocExceptTuple (k_fn finish) =
              some ((unionAllocRaw updated₁).extract 0 0 ++ srcRaw ++
                (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size,
                updated₁.byteSize, updated₁.provenanceMap, updated₁.initializationMask,
                updated₁.align, updated₁.mutability, updated₁.extra, updated₁.nativeBuffer)) ∧
            Except.ok updated₂ =
              (((Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).endExclusive |>.mapError
                Miri.Memory.AllocError.memory) >>= fun finish =>
                if (((unionAllocRaw updated₁).extract 0 0 ++ srcRaw ++
                    (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size !=
                    updated₁.byteSize.bytes.toNat) = true then
                  throw (Miri.Memory.AllocError.storageLengthMismatch updated₁.byteSize
                    ((unionAllocRaw updated₁).extract 0 0 ++ srcRaw ++
                      (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size)
                else k_fn finish) := by
          refine ⟨_, ?_, by rw [← hovw]; with_unfolding_all rfl⟩
          intro finish
          with_unfolding_all rfl
        rcases hovw2 with ⟨k_fn, hk_fn, hovw2⟩
        rw [hend] at hovw2
        dsimp only [Except.mapError, bind, Bind.bind, Except.bind] at hovw2
        rw [hSn] at hovw2
        induction updated₁ using Miri.Memory.Allocation.casesOn
        simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
        rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        unfold unionAllocRaw Miri.Memory.Allocation.byteSize at hovw2
        unfold unionAllocRaw Miri.Memory.Allocation.byteSize
          Miri.Memory.Allocation.provenanceMap Miri.Memory.Allocation.initializationMask
          Miri.Memory.Allocation.align Miri.Memory.Allocation.mutability
          Miri.Memory.Allocation.extra Miri.Memory.Allocation.nativeBuffer at hk_fn
        dsimp only at hovw2 hk_fn
        rw [hraw₁] at hovw2 hk_fn
        have hupd : destRaw.extract 0 0 ++ srcRaw ++ destRaw.extract S destRaw.size = srcRaw := by
          rw [hlen_dst]
          simp [Nat.min_le_left]
        rw [hupd, hSn, hlen_src, bne_self_eq_false] at hovw2
        simp only [Bool.false_eq_true, ↓reduceIte] at hovw2
        rw [hovw2]
        have hk_spec := hk_fn (translateSizeBytes S)
        rw [hSn, hupd] at hk_spec
        exact hk_spec
      have hmask_u2 : updated₂.initializationMask = ⟨.Lazy true, translateSizeBytes S⟩ := by
        induction updated₂ using Miri.Memory.Allocation.casesOn
        simp only [allocExceptTuple, Option.some.injEq, Prod.mk.injEq] at hu2
        rcases hu2 with ⟨_, _, _, rfl, _, _, _, _⟩
        rfl
      have hap := applyCopy_lazy_true hS hk hle
      rw [← hmask_u2] at hap
      unfold Miri.Memory.Allocation.initializationMask at hap
      rw [hap]
      apply of_allocResultTuple_eq_some srcRaw ?_ hlen_src
      induction updated₂ using Miri.Memory.Allocation.casesOn
      simp only [allocExceptTuple, Option.some.injEq, Prod.mk.injEq] at hu2
      rcases hu2 with ⟨hraw, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [hraw]
      rfl
    · rename_i _ reason hovw
      have hovw2 : ∃ (k_fn : Miri.ABI.Size → Except Miri.Memory.AllocError
          (Miri.Memory.Allocation AnnealProv E)),
          (∀ finish, allocExceptTuple (k_fn finish) =
            some ((unionAllocRaw updated₁).extract 0 0 ++ srcRaw ++
              (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size,
              updated₁.byteSize, updated₁.provenanceMap, updated₁.initializationMask,
              updated₁.align, updated₁.mutability, updated₁.extra, updated₁.nativeBuffer)) ∧
          Except.error reason =
            (((Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).endExclusive |>.mapError
              Miri.Memory.AllocError.memory) >>= fun finish =>
              if (((unionAllocRaw updated₁).extract 0 0 ++ srcRaw ++
                  (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size !=
                  updated₁.byteSize.bytes.toNat) = true then
                throw (Miri.Memory.AllocError.storageLengthMismatch updated₁.byteSize
                  ((unionAllocRaw updated₁).extract 0 0 ++ srcRaw ++
                    (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size)
              else k_fn finish) := by
        refine ⟨_, ?_, by rw [← hovw]; with_unfolding_all rfl⟩
        intro finish
        with_unfolding_all rfl
      rcases hovw2 with ⟨k_fn, hk_fn, hovw2⟩
      rw [hend] at hovw2
      dsimp only [Except.mapError, bind, Bind.bind, Except.bind] at hovw2
      rw [hSn] at hovw2
      induction updated₁ using Miri.Memory.Allocation.casesOn
      simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
      rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      unfold unionAllocRaw Miri.Memory.Allocation.byteSize at hovw2
      unfold unionAllocRaw Miri.Memory.Allocation.byteSize
        Miri.Memory.Allocation.provenanceMap Miri.Memory.Allocation.initializationMask
        Miri.Memory.Allocation.align Miri.Memory.Allocation.mutability
        Miri.Memory.Allocation.extra Miri.Memory.Allocation.nativeBuffer at hk_fn
      dsimp only at hovw2 hk_fn
      rw [hraw₁] at hovw2 hk_fn
      have hupd : destRaw.extract 0 0 ++ srcRaw ++ destRaw.extract S destRaw.size = srcRaw := by
        rw [hlen_dst]
        simp [Nat.min_le_left]
      rw [hupd, hSn, hlen_src, bne_self_eq_false] at hovw2
      simp only [Bool.false_eq_true, ↓reduceIte] at hovw2
      have hk_spec := hk_fn (translateSizeBytes S)
      rw [← hovw2] at hk_spec
      cases hk_spec
  · rename_i _ _ hprep_ovw
    have hpo := hprep_ovw
    with_unfolding_all
      conv at hpo => lhs; whnf
      rw [hslice_dst] at hpo
      dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
      simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
      conv at hpo => lhs; arg 2; whnf
      simp only [hset_dst, Except.mapError] at hpo
      dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
      rw [hclr_dst] at hpo
      cases hpo

set_option maxHeartbeats 800000 in
/-- Running `Miri.Memory.Allocation.copy` with `sameAllocation = true` and
`nonoverlapping = true` on a mutable `S`-byte union allocation `src` with at
least one initialized byte (`IsUnionPrefixMask S k`, `ValidScalarBytes k`) fails
with `AllocError.copyRangesOverlap` (`copy_nonoverlapping` self-copy UB). -/
theorem union_copy_self_overlap_err {E : Type}
    {src : Miri.Memory.Allocation AnnealProv E} {S k : Nat}
    (hS : ValidScalarBytes S) (hk : ValidScalarBytes k) (hle : k ≤ S)
    (hlen : src.len = S) (hsz : src.byteSize = translateSizeBytes S)
    (hmut : src.mutability = .Mut)
    (hprov : src.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : IsUnionPrefixMask S k src.initializationMask) :
    ∃ st' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copy src
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true src =
        .error .copyRangesOverlap st' := by
  have hS16 : S ≤ 16 := by rcases hS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hend : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).endExclusive =
      .ok (translateSizeBytes S) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hnz_sz : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size.bytes ==
      0) = false := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hpos_sz : (Miri.ABI.Size.ZERO.bytes < (translateSizeBytes S).bytes) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> decide
  have hslice : Miri.Memory.Allocation.getBytesUnchecked src
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok ((unionAllocRaw src).extract 0 S) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen hsz hS16 (Nat.le_refl S)]
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice
  have hprep_prov := provenanceMap_prepareCopy_new hS (unionAllocRaw src)
  unfold unionAllocRaw at hprep_prov
  have hno_uninit := unionInitCopy_noBytesInit hS hk hle
  have hmul : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size.mul 1 =
      .ok (translateSizeBytes S) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hmask_len := hmask.len_eq
  induction src using Miri.Memory.Allocation.casesOn
  rename_i srcRaw srcSz srcProv srcMask srcAlign srcMut srcExtra srcNat
  change srcRaw.size = S at hlen
  change srcSz = translateSizeBytes S at hsz
  change srcMut = .Mut at hmut
  change srcProv = Miri.Memory.ProvenanceMap.new at hprov
  change IsUnionPrefixMask S k srcMask at hmask
  change srcMask.len = translateSizeBytes S at hmask_len
  have hprep_mask := isUnionPrefixMask_prepareCopy hS hk hle hmask
  change _ = Except.ok (srcRaw.extract 0 S) at hslice
  change (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
      srcRaw (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ at hprep_prov
  subst hsz hmut hprov
  have hset_dst : srcMask.setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) true =
      .ok ⟨.Lazy true, translateSizeBytes S⟩ :=
    initMask_setRange_full_overwrite srcMask
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
      (translateSizeBytes S) true hend rfl (by rw [hmask_len]; exact UInt64.le_refl _)
  have hclr_dst := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) srcRaw
    (Miri.ABI.Size.ofBytes 8) (translateSizeBytes S) (by decide) hend
  unfold Miri.Memory.Allocation.copy Miri.Memory.Allocation.copyRepeatedly
  rw [hslice]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [hmul]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hslice]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_prov]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_mask]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  split
  · rename_i _ updated₁ _
    simp only [hno_uninit, Bool.false_eq_true, ↓reduceIte, Bool.and_self,
      show (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size =
        translateSizeBytes S from rfl,
      show (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).start =
        Miri.ABI.Size.ZERO from rfl,
      hend, hpos_sz, decide_true]
    exact ⟨updated₁, rfl⟩
  · rename_i _ _ hprep_ovw
    have hpo := hprep_ovw
    with_unfolding_all
      conv at hpo => lhs; whnf
      rw [hslice] at hpo
      dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
      simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
      conv at hpo => lhs; arg 2; whnf
      simp only [hset_dst, Except.mapError] at hpo
      dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
      rw [hclr_dst] at hpo
      cases hpo

set_option maxHeartbeats 800000 in
/-- Running `Miri.Memory.Allocation.copy` from a completely uninitialized
`S`-byte union allocation (`InitMask.new (translateSizeBytes S) false`, such as
`MaybeUninit::uninit()`) into any mutable `S`-byte destination allocation `dest`
takes `copyRepeatedly`'s `initialized.noBytesInit` fast path
(`Allocation.writeUninit`), succeeding for **any** `sameAlloc : Bool` (including
self-copy!) and resetting `dest.initializationMask` to
`InitMask.new (translateSizeBytes S) false`. -/
theorem union_copy_uninit_alloc_spec {E : Type}
    {src dest : Miri.Memory.Allocation AnnealProv E} {S : Nat}
    (hS : ValidScalarBytes S) (sameAlloc : Bool)
    (hlen_src : src.len = S) (hsz_src : src.byteSize = translateSizeBytes S)
    (hprov_src : src.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_src : src.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes S) false)
    (hlen_dst : dest.len = S) (hsz_dst : dest.byteSize = translateSizeBytes S)
    (hmut_dst : dest.mutability = .Mut)
    (hprov_dst : dest.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_dst : dest.initializationMask.len = translateSizeBytes S) :
    ∃ dest' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copy src
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) sameAlloc true dest = .ok () dest' ∧
      dest'.byteSize = translateSizeBytes S ∧
      dest'.len = S ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes S) false ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      unionAllocRaw dest' = unionAllocRaw dest := by
  have hS16 : S ≤ 16 := by rcases hS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hend : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).endExclusive =
      .ok (translateSizeBytes S) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hnz_sz : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size.bytes ==
      0) = false := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hslice_src : Miri.Memory.Allocation.getBytesUnchecked src
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok ((unionAllocRaw src).extract 0 S) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen_src hsz_src hS16 (Nat.le_refl S)]
  have hslice_dst : Miri.Memory.Allocation.getBytesUnchecked dest
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok ((unionAllocRaw dest).extract 0 S) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen_dst hsz_dst hS16 (Nat.le_refl S)]
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice_src hslice_dst
  have hprep_prov := provenanceMap_prepareCopy_new hS (unionAllocRaw src)
  unfold unionAllocRaw at hprep_prov
  have hprep_mask : (Miri.Memory.InitMask.new (translateSizeBytes S) false).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok ⟨false, #[UInt64.ofNat S]⟩ := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> with_unfolding_all rfl
  have hmul : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size.mul 1 =
      .ok (translateSizeBytes S) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  induction src using Miri.Memory.Allocation.casesOn
  rename_i srcRaw srcSz srcProv srcMask srcAlign srcMut srcExtra srcNat
  induction dest using Miri.Memory.Allocation.casesOn
  rename_i destRaw destSz destProv destMask destAlign destMut destExtra destNat
  change srcRaw.size = S at hlen_src
  change srcSz = translateSizeBytes S at hsz_src
  change srcProv = Miri.Memory.ProvenanceMap.new at hprov_src
  change srcMask = Miri.Memory.InitMask.new (translateSizeBytes S) false at hmask_src
  change destRaw.size = S at hlen_dst
  change destSz = translateSizeBytes S at hsz_dst
  change destMut = .Mut at hmut_dst
  change destProv = Miri.Memory.ProvenanceMap.new at hprov_dst
  change destMask.len = translateSizeBytes S at hmask_dst
  change _ = Except.ok (srcRaw.extract 0 S) at hslice_src
  change _ = Except.ok (destRaw.extract 0 S) at hslice_dst
  change (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
      srcRaw (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ at hprep_prov
  subst hsz_src hprov_src hmask_src hsz_dst hmut_dst hprov_dst
  have hset_dst : destMask.setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) true =
      .ok ⟨.Lazy true, translateSizeBytes S⟩ :=
    initMask_setRange_full_overwrite destMask
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
      (translateSizeBytes S) true hend rfl (by rw [hmask_dst]; exact UInt64.le_refl _)
  have hclr_dst := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) destRaw
    (Miri.ABI.Size.ofBytes 8) (translateSizeBytes S) (by decide) hend
  unfold Miri.Memory.Allocation.copy Miri.Memory.Allocation.copyRepeatedly
  rw [hslice_src]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [hmul]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hslice_dst]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_prov]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_mask]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  split
  · rename_i _ updated₁ hprep_ovw
    have hu1 : allocResultTuple (.ok () updated₁) =
        some (destRaw, translateSizeBytes S, Miri.Memory.ProvenanceMap.new,
          ⟨.Lazy true, translateSizeBytes S⟩, destAlign, .Mut, destExtra, destNat) := by
      have hpo := hprep_ovw
      with_unfolding_all
        conv at hpo => lhs; whnf
        rw [hslice_dst] at hpo
        dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
        simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
        conv at hpo => lhs; arg 2; whnf
        simp only [hset_dst, Except.mapError] at hpo
        dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
        rw [hclr_dst] at hpo
        cases hpo
        rfl
    have hno_init : (Miri.Memory.InitCopy.mk false #[UInt64.ofNat S]).noBytesInit = true := rfl
    simp only [hno_init, ↓reduceIte]
    have hlen_u1 : updated₁.len = S := by
      induction updated₁ using Miri.Memory.Allocation.casesOn
      simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
      rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact hraw₁ ▸ hlen_dst
    have hsz_u1 : updated₁.byteSize = translateSizeBytes S := by
      induction updated₁ using Miri.Memory.Allocation.casesOn
      simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
      rcases hu1 with ⟨_, rfl, _⟩; rfl
    have hslice_u1 : Miri.Memory.Allocation.getBytesUnchecked updated₁
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
        .ok ((unionAllocRaw updated₁).extract 0 S) := by
      rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen_u1 hsz_u1 hS16 (Nat.le_refl S)]
    unfold Miri.Memory.Allocation.getBytesUnchecked at hslice_u1
    have hset_uninit : (Miri.Memory.InitMask.mk (.Lazy true) (translateSizeBytes S)).setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) false =
        .ok (Miri.Memory.InitMask.new (translateSizeBytes S) false) :=
      initMask_setRange_full_overwrite _ _ _ false hend rfl (UInt64.le_refl _)
    split
    · rename_i _ _ hwu
      have hwu' := hwu
      induction updated₁ using Miri.Memory.Allocation.casesOn
      simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
      rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      cases hraw₁
      with_unfolding_all
        conv at hwu' => lhs; whnf
        rw [hslice_u1] at hwu'
        dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hwu'
        simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hwu'
        conv at hwu' => lhs; arg 2; whnf
        simp only [hset_uninit, Except.mapError] at hwu'
        dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hwu'
        rw [hclr_dst] at hwu'
        cases hwu'
    · rename_i updated₂ hwu
      have hu2 : allocResultTuple (.ok () updated₂) =
          some (destRaw, translateSizeBytes S, Miri.Memory.ProvenanceMap.new,
            Miri.Memory.InitMask.new (translateSizeBytes S) false,
            destAlign, .Mut, destExtra, destNat) := by
        have hwu' := hwu
        induction updated₁ using Miri.Memory.Allocation.casesOn
        simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
        rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        cases hraw₁
        with_unfolding_all
          conv at hwu' => lhs; whnf
          rw [hslice_u1] at hwu'
          dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hwu'
          simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hwu'
          conv at hwu' => lhs; arg 2; whnf
          simp only [hset_uninit, Except.mapError] at hwu'
          dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hwu'
          rw [hclr_dst] at hwu'
          cases hwu'
          rfl
      induction updated₂ using Miri.Memory.Allocation.casesOn
      simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu2
      rcases hu2 with ⟨hraw₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      cases hraw₂
      exact ⟨_, rfl, rfl, hlen_dst, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rename_i _ _ hprep_ovw
    have hpo := hprep_ovw
    with_unfolding_all
      conv at hpo => lhs; whnf
      rw [hslice_dst] at hpo
      dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
      simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
      conv at hpo => lhs; arg 2; whnf
      simp only [hset_dst, Except.mapError] at hpo
      dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
      rw [hclr_dst] at hpo
      cases hpo

set_option maxHeartbeats 800000 in
/-- Running `Miri.Memory.Allocation.copy` (`copyRepeatedly ... 1 ...`) from a
non-empty `ArraySliceRel` subslice at `srcOff` into **any** distinct mutable
`totalSz`-byte destination allocation `dest` (regardless of `dest`'s prior raw
bytes or initialization mask, so long as `dest.len = totalBytes` and
`dest.initializationMask.len = totalSz`) overwrites `dest` completely with
`InitMask.new totalSz true`, empty provenance, and
`ArraySliceRel elemKind cnt layouts elems Size.ZERO dest'`. -/
theorem array_copy_alloc_spec
    {elemKind : RigidTy} {cnt : Nat} {layouts : LayoutTable} {elems : List Value}
    {srcOff : Miri.ABI.Size}
    {src dest : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hslice : ArraySliceRel elemKind cnt layouts elems srcOff src)
    (hpos : 0 < cnt)
    (helem_pos : 0 < (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)
    (hlen_dst_in : dest.len =
      cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)
    (hsz_dst : dest.byteSize =
      Miri.ABI.Size.ofBytes
        (UInt64.ofNat
          (cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)))
    (hmut_dst : dest.mutability = .Mut)
    (hprov_dst : dest.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_dst : dest.initializationMask.len = dest.byteSize) :
    let totalBytes :=
      cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat
    let totalSz := Miri.ABI.Size.ofBytes (UInt64.ofNat totalBytes)
    ∃ dest' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      Miri.Memory.Allocation.copy src (Miri.Memory.allocRange srcOff totalSz)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true dest = .ok () dest' ∧
      dest'.byteSize = totalSz ∧
      dest'.len = totalBytes ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = Miri.Memory.InitMask.new totalSz true ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      ArraySliceRel elemKind cnt layouts elems Miri.ABI.Size.ZERO dest' := by
  intro totalBytes totalSz
  have htot_pos : 0 < totalBytes := Nat.mul_pos hpos helem_pos
  have hbs_src : src.byteSize.bytes.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have hin_src_nat : srcOff.bytes.toNat + totalBytes ≤ src.byteSize.bytes.toNat :=
    hslice.slice_in_bounds
  have htot_lt64 : totalBytes < 2 ^ 64 := by omega
  have htot_toNat : totalSz.bytes.toNat = totalBytes := by
    simp only [totalSz, Miri.ABI.Size.ofBytes, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt htot_lt64
  have hpos_sz : 0 < totalSz.bytes.toNat := by rw [htot_toNat]; exact htot_pos
  have hin_src : srcOff.bytes.toNat + totalSz.bytes.toNat ≤ src.byteSize.bytes.toNat := by
    rw [htot_toNat]; exact hin_src_nat
  have hlt_src : srcOff.bytes.toNat + totalSz.bytes.toNat < 2 ^ 64 := by omega
  have hsz_dst_eq : dest.byteSize = totalSz := hsz_dst
  have hlen_dst : dest.len = dest.byteSize.bytes.toNat := by
    rw [hlen_dst_in, hsz_dst_eq, htot_toNat]
  have hin_dst : Miri.ABI.Size.ZERO.bytes.toNat + totalSz.bytes.toNat ≤ dest.byteSize.bytes.toNat := by
    rw [hsz_dst_eq]; simp [Miri.ABI.Size.ZERO]
  have hslice_src := getBytesUnchecked_at (A := src) srcOff totalSz hslice.alloc_len hin_src
  have hslice_dst := getBytesUnchecked_at (A := dest) Miri.ABI.Size.ZERO totalSz hlen_dst hin_dst
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice_src hslice_dst
  have hprep_prov := provenanceMap_prepareCopy_new_at srcOff totalSz hlt_src (unionAllocRaw src)
  have hprep_mask := initMask_new_true_prepareCopy (srcSz := src.byteSize) hpos_sz hin_src
  have hmul : (Miri.Memory.allocRange srcOff totalSz).size.mul 1 = .ok totalSz := by
    simp [Miri.ABI.Size.mul, Miri.Memory.allocRange, Miri.ABI.Size.ofBytes]
  have hend_dst : (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).endExclusive = .ok totalSz := by
    have hlt0 : Miri.ABI.Size.ZERO.bytes.toNat + totalSz.bytes.toNat < 2 ^ 64 := by
      simp [Miri.ABI.Size.ZERO]
      exact UInt64.toNat_lt totalSz.bytes
    have h := allocRange_endExclusive_of_lt (off := Miri.ABI.Size.ZERO) (sz := totalSz) hlt0
    simpa [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes] using h
  have hloop (b : Array UInt8) :
      forIn [: (1 : UInt64).toNat] (#[] : Array UInt8) (fun _ r =>
        (pure (ForInStep.yield (r ++ b)) : Id (ForInStep (Array UInt8)))) = b := by
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
    rfl
  have hnz_sz : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).size.bytes == 0) = false := by
    cases h : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).size.bytes == 0) with
    | false => rfl
    | true =>
      have := eq_of_beq h
      dsimp [Miri.Memory.allocRange] at this
      rw [this] at hpos_sz
      simp at hpos_sz
  let copiedRaw := (unionAllocRaw src).extract srcOff.bytes.toNat
    (srcOff.bytes.toNat + totalSz.bytes.toNat)
  have hcopied_len : copiedRaw.size = totalBytes := by
    have hraw_src : (unionAllocRaw src).size = src.byteSize.bytes.toNat := hslice.alloc_len
    simp [copiedRaw, Array.size_extract, hraw_src, htot_toNat]
    omega
  have hcopy_res : ∃ dest' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      Miri.Memory.Allocation.copy src (Miri.Memory.allocRange srcOff totalSz)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true dest = .ok () dest' ∧
      dest'.byteSize = totalSz ∧
      dest'.len = totalBytes ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = Miri.Memory.InitMask.new totalSz true ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      unionAllocRaw dest' = copiedRaw := by
    have hprov_src := hslice.alloc_prov
    have hmask_src := hslice.alloc_mask
    have hmask_dst' : dest.initializationMask.len = totalSz := by
      rw [← hsz_dst_eq]; exact hmask_dst
    induction src using Miri.Memory.Allocation.casesOn
    rename_i srcRaw srcSz srcProv srcMask srcAlign srcMut srcExtra srcNat
    induction dest using Miri.Memory.Allocation.casesOn
    rename_i destRaw destSz destProv destMask destAlign destMut destExtra destNat
    change srcProv = Miri.Memory.ProvenanceMap.new at hprov_src
    change srcMask = Miri.Memory.InitMask.new srcSz true at hmask_src
    change destRaw.size = totalBytes at hlen_dst_in
    change destSz = totalSz at hsz_dst
    change destMut = .Mut at hmut_dst
    change destProv = Miri.Memory.ProvenanceMap.new at hprov_dst
    change destMask.len = totalSz at hmask_dst'
    change _ = Except.ok copiedRaw at hslice_src
    change _ = Except.ok (destRaw.extract 0 (0 + totalSz.bytes.toNat)) at hslice_dst
    change (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
        (Miri.Memory.allocRange srcOff totalSz) srcRaw (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ at hprep_prov
    change (Miri.Memory.InitMask.new srcSz true).prepareCopy
        (Miri.Memory.allocRange srcOff totalSz) = .ok ⟨true, #[totalSz.bytes]⟩ at hprep_mask
    subst hprov_src hmask_src hsz_dst hmut_dst hprov_dst
    unfold Miri.Memory.Allocation.copy Miri.Memory.Allocation.copyRepeatedly
    simp only [hloop]
    rw [hslice_src]
    dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
    rw [hmul]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [hslice_dst]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [hprep_prov]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [hprep_mask]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    have hno_init : (Miri.Memory.InitCopy.mk true #[totalSz.bytes]).noBytesInit = false := rfl
    simp only [hno_init, show ((1 : UInt64) == 0) = false from rfl,
      show (Miri.Memory.allocRange srcOff totalSz).size = totalSz from rfl,
      provenanceMap_applyCopy_empty, Bool.not_true, Bool.false_and, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]
    have hset_dst : destMask.setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz) true =
        .ok ⟨.Lazy true, totalSz⟩ :=
      initMask_setRange_full_overwrite destMask
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz) totalSz true hend_dst rfl
        (by rw [hmask_dst']; exact UInt64.le_refl _)
    have hclr_dst := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz) destRaw
      (Miri.ABI.Size.ofBytes 8) totalSz (by decide) hend_dst
    split
    · rename_i _ updated₁ hprep_ovw
      have hu1 : allocResultTuple (.ok () updated₁) =
          some (destRaw, totalSz, Miri.Memory.ProvenanceMap.new,
            ⟨.Lazy true, totalSz⟩, destAlign, .Mut, destExtra, destNat) := by
        have hpo := hprep_ovw
        with_unfolding_all
          conv at hpo => lhs; whnf
          rw [hslice_dst] at hpo
          dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
          simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
          conv at hpo => lhs; arg 2; whnf
          simp only [hset_dst, Except.mapError] at hpo
          dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
          rw [hclr_dst] at hpo
          cases hpo
          rfl
      split
      · rename_i _ updated₂ hovw
        have hu2 : allocExceptTuple (.ok updated₂) =
            some (copiedRaw, totalSz, Miri.Memory.ProvenanceMap.new,
              ⟨.Lazy true, totalSz⟩, destAlign, .Mut, destExtra, destNat) := by
          have hovw2 : ∃ (k_fn : Miri.ABI.Size → Except Miri.Memory.AllocError
              (Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))),
              (∀ finish, allocExceptTuple (k_fn finish) =
                some ((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                  (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size,
                  updated₁.byteSize, updated₁.provenanceMap, updated₁.initializationMask,
                  updated₁.align, updated₁.mutability, updated₁.extra, updated₁.nativeBuffer)) ∧
              Except.ok updated₂ =
                (((Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).endExclusive |>.mapError
                  Miri.Memory.AllocError.memory) >>= fun finish =>
                  if (((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                      (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size !=
                      updated₁.byteSize.bytes.toNat) = true then
                    throw (Miri.Memory.AllocError.storageLengthMismatch updated₁.byteSize
                      ((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                        (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size)
                  else k_fn finish) := by
            refine ⟨_, ?_, by rw [← hovw]; with_unfolding_all rfl⟩
            intro finish
            with_unfolding_all rfl
          rcases hovw2 with ⟨k_fn, hk_fn, hovw2⟩
          rw [hend_dst] at hovw2
          dsimp only [Except.mapError, bind, Bind.bind, Except.bind] at hovw2
          induction updated₁ using Miri.Memory.Allocation.casesOn
          simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
          rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          unfold unionAllocRaw Miri.Memory.Allocation.byteSize at hovw2
          unfold unionAllocRaw Miri.Memory.Allocation.byteSize
            Miri.Memory.Allocation.provenanceMap Miri.Memory.Allocation.initializationMask
            Miri.Memory.Allocation.align Miri.Memory.Allocation.mutability
            Miri.Memory.Allocation.extra Miri.Memory.Allocation.nativeBuffer at hk_fn
          dsimp only at hovw2 hk_fn
          rw [hraw₁] at hovw2 hk_fn
          have hupd : destRaw.extract 0 0 ++ copiedRaw ++
              destRaw.extract totalSz.bytes.toNat destRaw.size = copiedRaw := by
            rw [htot_toNat, hlen_dst_in]
            simp [Nat.min_le_left]
          rw [hupd, hcopied_len, htot_toNat, bne_self_eq_false] at hovw2
          simp only [Bool.false_eq_true, ↓reduceIte] at hovw2
          rw [hovw2]
          have hk_spec := hk_fn totalSz
          rw [hupd] at hk_spec
          exact hk_spec
        have hmask_u2 : updated₂.initializationMask = ⟨.Lazy true, totalSz⟩ := by
          induction updated₂ using Miri.Memory.Allocation.casesOn
          simp only [allocExceptTuple, Option.some.injEq, Prod.mk.injEq] at hu2
          rcases hu2 with ⟨_, _, _, rfl, _, _, _, _⟩
          rfl
        have hap := initMask_applyCopy_full totalSz hpos_sz
        rw [← hmask_u2] at hap
        unfold Miri.Memory.Allocation.initializationMask at hap
        rw [hap]
        dsimp only [bind, Bind.bind, pure, Pure.pure]
        induction updated₂ using Miri.Memory.Allocation.casesOn
        simp only [allocExceptTuple, Option.some.injEq, Prod.mk.injEq] at hu2
        rcases hu2 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact ⟨_, rfl, rfl, hcopied_len, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rename_i _ reason hovw
        have hovw2 : ∃ (k_fn : Miri.ABI.Size → Except Miri.Memory.AllocError
            (Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))),
            (∀ finish, allocExceptTuple (k_fn finish) =
              some ((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size,
                updated₁.byteSize, updated₁.provenanceMap, updated₁.initializationMask,
                updated₁.align, updated₁.mutability, updated₁.extra, updated₁.nativeBuffer)) ∧
            Except.error reason =
              (((Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).endExclusive |>.mapError
                Miri.Memory.AllocError.memory) >>= fun finish =>
                if (((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                    (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size !=
                    updated₁.byteSize.bytes.toNat) = true then
                  throw (Miri.Memory.AllocError.storageLengthMismatch updated₁.byteSize
                    ((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                      (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size)
                else k_fn finish) := by
          refine ⟨_, ?_, by rw [← hovw]; with_unfolding_all rfl⟩
          intro finish
          with_unfolding_all rfl
        rcases hovw2 with ⟨k_fn, hk_fn, hovw2⟩
        rw [hend_dst] at hovw2
        dsimp only [Except.mapError, bind, Bind.bind, Except.bind] at hovw2
        induction updated₁ using Miri.Memory.Allocation.casesOn
        simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
        rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        unfold unionAllocRaw Miri.Memory.Allocation.byteSize at hovw2
        unfold unionAllocRaw Miri.Memory.Allocation.byteSize
          Miri.Memory.Allocation.provenanceMap Miri.Memory.Allocation.initializationMask
          Miri.Memory.Allocation.align Miri.Memory.Allocation.mutability
          Miri.Memory.Allocation.extra Miri.Memory.Allocation.nativeBuffer at hk_fn
        dsimp only at hovw2 hk_fn
        rw [hraw₁] at hovw2 hk_fn
        have hupd : destRaw.extract 0 0 ++ copiedRaw ++
            destRaw.extract totalSz.bytes.toNat destRaw.size = copiedRaw := by
          rw [htot_toNat, hlen_dst_in]
          simp [Nat.min_le_left]
        rw [hupd, hcopied_len, htot_toNat, bne_self_eq_false] at hovw2
        simp only [Bool.false_eq_true, ↓reduceIte] at hovw2
        have hk_spec := hk_fn totalSz
        rw [← hovw2] at hk_spec
        cases hk_spec
    · rename_i _ _ hprep_ovw
      have hpo := hprep_ovw
      with_unfolding_all
        conv at hpo => lhs; whnf
        rw [hslice_dst] at hpo
        dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
        simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
        conv at hpo => lhs; arg 2; whnf
        simp only [hset_dst, Except.mapError] at hpo
        dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
        rw [hclr_dst] at hpo
        cases hpo
  obtain ⟨dest', hcopy, hsz', hlen', hal', hmut', hprov', hmask', hex', hnat', hraw'⟩ := hcopy_res
  refine ⟨dest', hcopy, hsz', hlen', hal', hmut', hprov', hmask', hex', hnat', ?_⟩
  refine
    { elems_len := hslice.elems_len
      alloc_len := by rw [hlen', hsz', htot_toNat]
      alloc_mut := hmut'
      alloc_prov := hprov'
      alloc_mask := by rw [hmask', hsz']
      slice_in_bounds := by
        rw [hsz', htot_toNat]; simp [Miri.ABI.Size.ZERO]; exact Nat.le_refl totalBytes
      elem_rel := ?_ }
  intro k elemVal hget
  have hk_lt : k < cnt := by
    rw [← hslice.elems_len]
    exact (List.getElem?_eq_some_iff.mp (by rwa [← get?_eq_getElem?])).1
  obtain ⟨sc, msc, hv, hesz, hbool, hchar, hrel, hread_src⟩ := hslice.elem_rel k elemVal hget
  refine ⟨sc, msc, hv, hesz, hbool, hchar, hrel, ?_⟩
  let elemLay := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout
  let es := elemLay.size.bytes.toNat
  have hk1_le : (k + 1) * es ≤ totalBytes := Nat.mul_le_mul_right _ (by omega)
  have hmul_add : (k + 1) * es = k * es + es := Nat.add_mul k 1 es |>.trans (by simp)
  have hkes_le : k * es + es ≤ totalBytes := by rw [← hmul_add]; exact hk1_le
  let dstElemOff := Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + UInt64.ofNat (k * es))
  let srcElemOff := Miri.ABI.Size.ofBytes (srcOff.bytes + UInt64.ofNat (k * es))
  have hdstOff_nat : dstElemOff.bytes.toNat = k * es := by
    simp only [dstElemOff, Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO, UInt64.zero_add,
      UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hsrcOff_nat : srcElemOff.bytes.toNat = srcOff.bytes.toNat + k * es := by
    have h1 : k * es < 2 ^ 64 := by omega
    have h2 : srcOff.bytes.toNat + k * es < 2 ^ 64 := by omega
    simp only [srcElemOff, Miri.ABI.Size.ofBytes, UInt64.toNat_add, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt h1]
    exact Nat.mod_eq_of_lt h2
  have hin_elem_dst : dstElemOff.bytes.toNat + es ≤ dest'.byteSize.bytes.toNat := by
    rw [hdstOff_nat, hsz', htot_toNat]; exact hkes_le
  have hin_elem_src : srcElemOff.bytes.toNat + es ≤ src.byteSize.bytes.toNat := by
    rw [hsrcOff_nat]; omega
  have hend_elem_dst := allocRange_endExclusive_of_lt
    (off := dstElemOff) (sz := elemLay.size)
    (by change dstElemOff.bytes.toNat + es < 2 ^ 64; omega)
  have hend_elem_src := allocRange_endExclusive_of_lt
    (off := srcElemOff) (sz := elemLay.size)
    (by change srcElemOff.bytes.toNat + es < 2 ^ 64; omega)
  have hinit_dst : dest'.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange dstElemOff elemLay.size) = .ok (.ok ()) := by
    rw [hmask']
    apply Miri.Memory.InitMask.lazy_initialized_query _ _ _ hend_elem_dst
    rw [UInt64.le_iff_toNat_le]
    have hfin_d : (Miri.ABI.Size.ofBytes (dstElemOff.bytes + elemLay.size.bytes)).bytes.toNat =
        dstElemOff.bytes.toNat + es := by
      simp only [Miri.ABI.Size.ofBytes, UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by change dstElemOff.bytes.toNat + es < 2 ^ 64; omega)
    rw [hfin_d, htot_toNat, hdstOff_nat]
    exact hkes_le
  have hinit_src : src.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange srcElemOff elemLay.size) = .ok (.ok ()) := by
    rw [hslice.alloc_mask]
    apply Miri.Memory.InitMask.lazy_initialized_query _ _ _ hend_elem_src
    rw [UInt64.le_iff_toNat_le]
    have hfin_s : (Miri.ABI.Size.ofBytes (srcElemOff.bytes + elemLay.size.bytes)).bytes.toNat =
        srcElemOff.bytes.toNat + es := by
      simp only [Miri.ABI.Size.ofBytes, UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by change srcElemOff.bytes.toNat + es < 2 ^ 64; omega)
    rw [hfin_s]
    exact hin_elem_src
  have hbytes_dst := getBytesUnchecked_at (A := dest') dstElemOff elemLay.size
    (by rw [hlen', hsz', htot_toNat]) hin_elem_dst
  have hbytes_src := getBytesUnchecked_at (A := src) srcElemOff elemLay.size
    hslice.alloc_len hin_elem_src
  have hextr_eq : (unionAllocRaw dest').extract dstElemOff.bytes.toNat
      (dstElemOff.bytes.toNat + es) =
      (unionAllocRaw src).extract srcElemOff.bytes.toNat (srcElemOff.bytes.toNat + es) := by
    rw [hraw']
    dsimp only [copiedRaw]
    rw [Array.extract_extract, hdstOff_nat, hsrcOff_nat, htot_toNat]
    congr 1
    omega
  change dest'.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange dstElemOff elemLay.size) false = _
  change src.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange srcElemOff elemLay.size) false = _ at hread_src
  rw [u_readScalar_eq] at hread_src ⊢
  unfold uReadScalar at hread_src ⊢
  rw [hinit_dst, hbytes_dst]
  rw [hinit_src, hbytes_src] at hread_src
  dsimp only [es] at hextr_eq
  rw [hextr_eq]
  exact hread_src

/-! ## 9. Union State Relation

`StateRel`'s `MemPlaceRel` requires every byte of an initialized memory-backed
local to be initialized (`val_consistent`), so it cannot relate a union whose
smaller field was written. `StateRelLM2_4` extends `StateRel` with two ways to
relate an initialized `n`-field Anneal union to a memory-backed `UnionMemRel`
allocation whose bytes `[0, k)` (`k = sc.sizeBytes`) hold `sc` and are
initialized while its trailing bytes `[k, S)` are not:
* `UnionLocalRel.union`: a plain single-active-field union
  `Value.aggregate 0 (unionSlotFields n f (.scalar sc))` (`f < n`, matching
  `evalAggregateAdtUnionValue?` and same-or-wider `rebuildUnionFieldsAfterWriteOpt`);
* `UnionLocalRel.unionOverlay`: a union carrying a `D13a` raw-byte overlay
  `Value.aggregate 0 (unionSlotFields n j (.scalar sc_low) ++ [.aggregate 0 (encodeRawAbstractByteVals mergedBytes)])`
  after a narrower projected scalar field write (`sc_low.sizeBytes < sc.sizeBytes`,
  `UnionOverlaySlotSpec`).
Every `StateRel` is a `StateRelLM2_4` (`StateRel.toLM2_4`). -/

/-- The `n`-slot Anneal field list of a union whose active field `f < n` holds `v`
and whose remaining `n - 1` sibling slots hold `.unit`, matching both
`evalAggregateAdtUnionValue?` and `rebuildUnionFieldsAfterWriteOpt`. -/
def unionSlotFields (n f : Nat) (v : Value) : List Value :=
  appendValueList (replicateValue f .unit) (v :: replicateValue (Nat.sub n (.succ f)) .unit)

private theorem valueListContainsUninit_replicateValue_unit :
    ∀ k : Nat, valueListContainsUninit (replicateValue k .unit) = false
  | 0 => rfl
  | k + 1 => by
    dsimp only [replicateValue, valueListContainsUninit, valueContainsUninit]
    exact valueListContainsUninit_replicateValue_unit k

private theorem valueListContainsUninit_appendValueList :
    ∀ (xs ys : List Value),
      valueListContainsUninit xs = false →
      valueListContainsUninit ys = false →
      valueListContainsUninit (appendValueList xs ys) = false
  | [], ys, _, hy => hy
  | x :: xs, ys, hx, hy => by
    dsimp only [appendValueList, valueListContainsUninit] at hx ⊢
    cases hvc : valueContainsUninit x <;> rw [hvc] at hx
    · exact valueListContainsUninit_appendValueList xs ys hx hy
    · cases hx

theorem valueContainsUninit_unionSlotFields_scalar (n f : Nat) (sc : MirAst.ScalarInt) :
    valueContainsUninit (.aggregate 0 (unionSlotFields n f (.scalar sc))) = false := by
  dsimp only [valueContainsUninit, unionSlotFields]
  refine valueListContainsUninit_appendValueList _ _
    (valueListContainsUninit_replicateValue_unit f) ?_
  dsimp only [valueListContainsUninit, valueContainsUninit]
  exact valueListContainsUninit_replicateValue_unit (Nat.sub n (.succ f))

/-- A union of `S ∈ {1, 2, 4, 8, 16}` bytes: its `lean-miri` layout has
`FieldsShape.Union` with at least one field, size `S`, an alignment that
`Align.fromBytes` accepts, `uTy.layoutIdx ∈ (0, 900)` (so `100 + uTy.layoutIdx < 1000`
stays inside `LeanMiriSpec.Translate`'s ADT `TyId` range in `unionFieldLayoutOf`),
and a well-formed `FieldsShape.union` entry in `layouts` whose scalar
`fieldLayouts` match `encodeByLayoutIdxAux`. -/
structure WellTypedUnionTy (layouts : LayoutTable) (uTy : Ty) (S : Nat) : Prop where
  size_valid : ValidScalarBytes S
  fields_union : ∃ n, (translateTy uTy layouts).layout.fields = .Union n ∧ 0 < n
  size_eq : (translateTy uTy layouts).layout.size = translateSizeBytes S
  sized : (translateTy uTy layouts).layout.isSized = true
  align_le : (translateTy uTy layouts).layout.align.abi.pow2 ≤ 29
  adt_spec : ∃ defPath args tl n,
    uTy.kind = .adt defPath args ∧
    0 < uTy.layoutIdx ∧
    uTy.layoutIdx < 900 ∧
    layouts.lookup uTy.layoutIdx = some tl ∧
    tl.fields = .union n ∧
    tl.variants = .single 0 ∧
    tl.isUninhabited = false ∧
    tl.size.bytes = S ∧
    tl.fieldLayouts.length = n ∧
    layouts.pointerBits = 64 ∧
    layouts.isLittleEndian = true ∧
    ∀ idx flIdx, get? tl.fieldLayouts idx = some flIdx →
      ∃ fTl, layouts.lookup flIdx = some fTl ∧
        fTl.isUninhabited = false ∧
        ValidScalarBytes fTl.size.bytes ∧
        fTl.size.bytes ≤ S ∧
        ∀ (fTy : Ty) (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt),
          IsPrimScalarTy fTy →
          ImmediateRel fTy layouts (.scalar sc) (.scalar (.fromScalarInt msc)) →
          sc.sizeBytes = fTl.size.bytes →
          ∀ fuel', encodeByLayoutIdxAux (fuel' + 1) layouts flIdx (.scalar sc) =
            encodeScalarBytes sc .none

/-- Construct a `WellTypedUnionTy` from purely structural layout facts whenever
every union field layout `fTl` has a full-range scalar (or non-range-restricted)
`backendRepr` (`vr.start = 0 ∧ vr.end_ + 1 = scalarModulus fTl.size.bytes`),
discharging the `encodeByLayoutIdxAux` codec clause once and for all. -/
theorem WellTypedUnionTy.of_fullRangeScalarFields
    {layouts : LayoutTable} {uTy : Ty} {S : Nat}
    (hsz : ValidScalarBytes S)
    (hfu : ∃ n, (translateTy uTy layouts).layout.fields = .Union n ∧ 0 < n)
    (hsize : (translateTy uTy layouts).layout.size = translateSizeBytes S)
    (hsized : (translateTy uTy layouts).layout.isSized = true)
    (halign : (translateTy uTy layouts).layout.align.abi.pow2 ≤ 29)
    {defPath : DefPath} {args : List RigidTy} {tl : TypeLayout} {n : Nat}
    (hkind : uTy.kind = .adt defPath args)
    (hidx_pos : 0 < uTy.layoutIdx)
    (hidx_lt : uTy.layoutIdx < 900)
    (hlook : layouts.lookup uTy.layoutIdx = some tl)
    (htl_fields : tl.fields = .union n)
    (htl_var : tl.variants = .single 0)
    (htl_uninh : tl.isUninhabited = false)
    (htl_sz : tl.size.bytes = S)
    (htl_len : tl.fieldLayouts.length = n)
    (hptr : layouts.pointerBits = 64)
    (hle : layouts.isLittleEndian = true)
    (hfields : ∀ idx flIdx, get? tl.fieldLayouts idx = some flIdx →
      ∃ fTl, layouts.lookup flIdx = some fTl ∧
        fTl.isUninhabited = false ∧
        ValidScalarBytes fTl.size.bytes ∧
        fTl.size.bytes ≤ S ∧
        (∀ prim vr, fTl.backendRepr = .scalar (.initialized prim vr) →
          vr.start = 0 ∧ vr.end_ + 1 = scalarModulus fTl.size.bytes)) :
    WellTypedUnionTy layouts uTy S where
  size_valid := hsz
  fields_union := hfu
  size_eq := hsize
  sized := hsized
  align_le := halign
  adt_spec := by
    refine ⟨defPath, args, tl, n, hkind, hidx_pos, hidx_lt, hlook, htl_fields, htl_var,
      htl_uninh, htl_sz, htl_len, hptr, hle, ?_⟩
    intro idx flIdx hget
    obtain ⟨fTl, hfTl, huninh, hfSz, hfLe, hfull⟩ := hfields idx flIdx hget
    refine ⟨fTl, hfTl, huninh, hfSz, hfLe, ?_⟩
    intro fTy sc msc _ himm hsc_sz fuel'
    cases himm with
    | scalar _ _ hrel _ _ _ =>
      have hcan := hrel.canonical
      rcases sc with ⟨bits, sz⟩
      dsimp only at hsc_sz hcan
      have hlookup : LayoutTable.lookup layouts flIdx = some fTl := hfTl
      unfold encodeByLayoutIdxAux
      rw [hlookup]
      rcases fTl with ⟨fSize, fAlign, fRepr, fFields, fVariants, fUninh, fLays⟩
      dsimp only at huninh hfSz hfull hsc_sz ⊢
      subst huninh hsc_sz
      dsimp only []
      have hble1 : Nat.ble 1 fSize.bytes = true := by
        rcases hfSz with h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> rfl
      have hbeqSz : Nat.beq fSize.bytes fSize.bytes = true := Nat.beq_refl fSize.bytes
      rw [hble1]
      dsimp only []
      rw [hbeqSz]
      dsimp only []
      cases fRepr with
      | memory => rfl
      | scalarPair _ _ => rfl
      | scalar sl =>
        cases sl with
        | union _ => rfl
        | initialized prim vr =>
          obtain ⟨hvs, hve⟩ := hfull prim vr rfl
          have hbits_le : bits ≤ vr.end_ := by omega
          have hse : Nat.ble vr.start vr.end_ = true := Nat.ble_eq.mpr (by omega)
          have hsv : Nat.ble vr.start bits = true := Nat.ble_eq.mpr (by omega)
          have hve_b : Nat.ble bits vr.end_ = true := Nat.ble_eq.mpr hbits_le
          have hw : wrappingRangeContains vr bits = true := by
            unfold wrappingRangeContains
            simp [hse, hsv, hve_b]
          have hnot_char : Nat.beq vr.end_ 0x10FFFF = false := by
            rcases hfSz with h1 | h1 | h1 | h1 | h1
            · rw [h1] at hve; have : vr.end_ = 255 := by simpa [scalarModulus] using hve
              rw [this]; rfl
            · rw [h1] at hve; have : vr.end_ = 65535 := by simpa [scalarModulus] using hve
              rw [this]; rfl
            · rw [h1] at hve; have : vr.end_ = 4294967295 := by simpa [scalarModulus] using hve
              rw [this]; rfl
            · rw [h1] at hve
              have : vr.end_ = 18446744073709551615 := by simpa [scalarModulus] using hve
              rw [this]; rfl
            · rw [h1] at hve
              have : vr.end_ = 340282366920938463463374607431768211455 := by
                simpa [scalarModulus] using hve
              rw [this]; rfl
          dsimp only []
          rw [hw]
          simp [hvs, hnot_char]

/-- A memory-backed union local `mp` whose active scalar field (of type `f0Ty`)
holds `sc`: `mp` points at offset `0` of its own live allocation, which has `S`
bytes, is mutable, has no provenance, Tree Borrows extra, or native buffer, has
the union's alignment, initializes `[0, k)` and leaves `[k, S)` uninitialized
for `k = sc.sizeBytes ≤ S` (`IsUnionPrefixMask`), and stores the little-endian
encoding of `sc` in `[0, k)`. -/
inductive UnionMemRel (mach : AnnealMachine) (uTy : Ty) (layouts : LayoutTable) (S : Nat)
    (f0Ty : Ty) (sc : MirAst.ScalarInt) (mp : Miri.Interpreter.MemPlace AnnealProv) : Prop where
  | mk
      (allocId : Miri.Memory.AllocId)
      (tag : Miri.Memory.BorTag)
      (baseAddr : UInt64)
      (localAlloc :
        Miri.Memory.LocalAllocation
          AnnealProv
          (Option Miri.TreeBorrows.BorrowTree)
          Miri.Memory.MiriMemoryKind)
      (msc : Miri.Memory.ScalarInt)
      (ptr_prov : mp.ptr.provenance = some (.concrete allocId tag))
      (no_misalign : mp.misaligned = none)
      (thin_meta : mp.metadata = .none)
      (live_lookup : (allocId, localAlloc) ∈ mach.memory.live.toList)
      (base_lookup : mach.lookupBaseAddr allocId = some baseAddr)
      (ptr_addr_eq : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
      (addr_no_overflow : baseAddr.toNat + S < 2 ^ 64)
      (alloc_size : localAlloc.allocation.byteSize = translateSizeBytes S)
      (alloc_len : localAlloc.allocation.len = S)
      (alloc_mut : localAlloc.allocation.mutability = .Mut)
      (alloc_prov : localAlloc.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
      (alloc_align : localAlloc.allocation.align = (translateTy uTy layouts).layout.align.abi)
      (alloc_extra : localAlloc.allocation.extra = none)
      (alloc_native : localAlloc.allocation.nativeBuffer = none)
      (k_le : sc.sizeBytes ≤ S)
      (mask : IsUnionPrefixMask S sc.sizeBytes localAlloc.allocation.initializationMask)
      (sc_rel : ScalarRel sc msc)
      (f0_prim : IsPrimScalarTy f0Ty)
      (f0_imm : ImmediateRel f0Ty layouts (.scalar sc) (.scalar (.fromScalarInt msc)))
      (raw : (unionAllocRaw localAlloc.allocation).extract 0 sc.sizeBytes =
        allocLeBytes sc.bits sc.sizeBytes) :
      UnionMemRel mach uTy layouts S f0Ty sc mp

/-- Witness that typed slot `(j_low, sc_low)` and raw-byte overlay `mergedBytes`
form a well-typed `D13a` overlay union representation for byte image
`encodeLittleEndianBytes sc.bits sc.sizeBytes none ++ replicateUninitBytes (S - sc.sizeBytes)`. -/
structure UnionOverlaySlotSpec
    (layouts : LayoutTable) (uTy : Ty) (S n j_low : Nat)
    (sc sc_low : MirAst.ScalarInt) (mergedBytes : List AbstractByte) : Prop where
  j_lt : j_low < n
  low_lt : sc_low.sizeBytes < sc.sizeBytes
  field_typed :
    ∃ (fLowTy : Ty) (msc_low : Miri.Memory.ScalarInt) (fl : Miri.Interpreter.LocalLayout),
      IsPrimScalarTy fLowTy ∧
      ImmediateRel fLowTy layouts (.scalar sc_low) (.scalar (.fromScalarInt msc_low)) ∧
      unionFieldLayoutOf layouts (translateTy uTy layouts) j_low = some fl ∧
      fl.layout.size = (translateTy fLowTy layouts).layout.size
  low_prefix :
    ∃ highBytes,
      encodeLittleEndianBytes sc.bits sc.sizeBytes none =
        encodeLittleEndianBytes sc_low.bits sc_low.sizeBytes none ++ highBytes
  bytes_eq :
    mergedBytes =
      encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
        replicateUninitBytes (S - sc.sizeBytes)

/-- `LocalRel` extended with initialized unions (`UnionMemRel`), covering both
plain single-active-field union values (`union`) and `D13a` raw-byte-overlay
union values produced by narrower projected field writes (`unionOverlay`). -/
inductive UnionLocalRel
    (mach : AnnealMachine)
    (decl : LocalDecl)
    (layouts : LayoutTable) :
    LocalSlot →
    Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout →
    Prop where
  /-- Any `LocalRel`-related pair. -/
  | base (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
      LocalRel mach decl layouts slot mls →
      UnionLocalRel mach decl layouts slot mls
  /-- An initialized `n`-field union holding active field `f`'s (`f < n`) value `sc`. -/
  | union (S n f : Nat) (f0Ty : Ty) (sc : MirAst.ScalarInt)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      WellTypedUnionTy layouts decl.ty S →
      (translateTy decl.ty layouts).layout.fields = .Union n →
      f < n →
      UnionMemRel mach decl.ty layouts S f0Ty sc mp →
      UnionLocalRel mach decl layouts
        (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))
        ⟨.live (.indirect mp), cachedLayout⟩
  /-- An initialized `n`-field union carrying a `D13a` raw-byte overlay after a
  narrower projected scalar field write `_u.j = sc_low` (`sc_low.sizeBytes < sc.sizeBytes ≤ S`),
  whose initialized `[0, sc.sizeBytes)` prefix represents `sc` (`UnionMemRel`). -/
  | unionOverlay (S n j : Nat) (f0Ty : Ty) (sc sc_low : MirAst.ScalarInt)
      (mergedBytes : List AbstractByte)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      WellTypedUnionTy layouts decl.ty S →
      (translateTy decl.ty layouts).layout.fields = .Union n →
      UnionOverlaySlotSpec layouts decl.ty S n j sc sc_low mergedBytes →
      UnionMemRel mach decl.ty layouts S f0Ty sc mp →
      UnionLocalRel mach decl layouts
        (.init (.aggregate 0
          (unionSlotFields n j (.scalar sc_low) ++
            [.aggregate 0 (encodeRawAbstractByteVals mergedBytes)])))
        ⟨.live (.indirect mp), cachedLayout⟩

/-- `FrameRel` with `UnionLocalRel` in place of `LocalRel`. -/
structure FrameRelLM2_4
    (body : CapturedMir)
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
      UnionLocalRel mach decl body.layouts slot mls

/-- `StateRel` with `FrameRelLM2_4` in place of `FrameRel`. -/
inductive StateRelLM2_4
    (body : CapturedMir)
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
      (frame_rel : FrameRelLM2_4 body m.machine s.frame topFrame)
      (activeCallee_none : s.memory.activeCallee = none)
      (callStack_nil : s.memory.callStack = .nil)
      (borrows_nil : s.memory.borrows = .nil)
      (activeProtectors_nil : s.memory.activeProtectors = .nil)
      (callerLocals_nil : s.memory.callerLocals = .nil)
      (memoryAllocDisjoint : MemoryAllocDisjoint topFrame) :
      StateRelLM2_4 body s m

/-- Every `StateRel` is a `StateRelLM2_4`. -/
theorem StateRel.toLM2_4 {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRel body s m) : StateRelLM2_4 body s m := by
  rcases h with ⟨tf, hf, hrc, hrp, hfr, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  exact ⟨tf, hf, hrc, hrp,
    ⟨hfr.body_eq, hfr.location_eq, hfr.af_locals_len, hfr.mf_locals_size,
      fun i d sl ml hd hs hm => .base sl ml (hfr.locals_rel i d sl ml hd hs hm)⟩,
    hcal, hst, hbor, hprot, hcaller, hdisj⟩

/-- A `StateRelLM2_4` in which every local is `LocalRel`-related is a
`StateRel`. -/
theorem StateRelLM2_4.toStateRel {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRelLM2_4 body s m)
    (hbase : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ (i : Nat) (decl : LocalDecl) (slot : LocalSlot)
        (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
        get? body.localDecls i = some decl →
        get? s.frame.locals i = some slot →
        topFrame.locals[i]? = some mls →
        LocalRel m.machine decl body.layouts slot mls) :
    StateRel body s m := by
  rcases h with ⟨tf, hf, hrc, hrp, hfr, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  exact ⟨tf, hf, hrc, hrp,
    ⟨hfr.body_eq, hfr.location_eq, hfr.af_locals_len, hfr.mf_locals_size,
      fun i d sl ml hd hs hm => hbase tf hf i d sl ml hd hs hm⟩,
    hcal, hst, hbor, hprot, hcaller, hdisj⟩

/-- `StepRel` with `StateRelLM2_4` in place of `StateRel`: both machines take a
normal step to related states, or both report undefined behavior. -/
inductive StepRelLM2_4 (body : CapturedMir) (m : AnnealStepState) :
    MirStepNode →
    Miri.Interpreter.StepResult AnnealStepState Bool →
    Prop where
  | step (s' : MachineState) (m' : AnnealStepState) :
      StateRelLM2_4 body s' m' →
      StepRelLM2_4 body m (MirStepNode.step s') (m', .ok true)
  | ub (m' : AnnealStepState) (msg : String) :
      StepRelLM2_4 body m (MirStepNode.fail .ub) (m', .error (.undefinedBehavior msg))


end LeanMiriSpec.Correspondence
