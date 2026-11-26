/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Proto.Ucg558PtrByteCoherenceProto
import Lean.Elab.Command

/-!
# Kernel-checked tests for `Anneal.Proto.Ucg558PtrByteCoherenceProto`

1. Concrete non-vacuity instantiations of every universal theorem (64-bit and 32-bit pointer
   widths, `offsetBytes = 0`, `p` vs `p + 256`, un-normalized offsets, exact `tag`
   preservation with `tag ≠ allocId`, wide `dyn` / slice pointers, in-order byte copies,
   Option 2 fail-closed migration, Miri and MiniRust bridges, read-time validity).
2. Independent `rfl` checks of the prototype decoders on the adversarial W1/W2/W3 inputs and
   the `Kani#5205` scenario chains (`MaybeUninit<bool>`, `Unaligned<bool>` at offset `1`,
   nested `MaybeUninit<Unaligned<bool>>`, `char` surrogate, `write_bytes`).
3. Restatements of every concrete live witness (`V2026_06_01`, `V2026_08_01`, MiniRust, Miri).
4. A trailing mechanical `MetaM` axiom audit with a non-vacuity reachability check.
-/

namespace Anneal.Ucg558PtrByteCoherenceProtoTests

open Anneal.Proto.Ucg558PtrByteCoherenceProto

/-! ## 1. Universal theorems, instantiated -/

def pZero : ProvenancePtrProto := ⟨1, 1, 0⟩
def p256 : ProvenancePtrProto := ⟨1, 1, 256⟩
def pBig : ProvenancePtrProto := ⟨3, 7, 0x1122334455667788⟩
def pBig4 : ProvenancePtrProto := ⟨3, 7, 0x11223344⟩
def pTag : ProvenancePtrProto := ⟨5, 9, 0x40⟩
def pVt : ProvenancePtrProto := ⟨2, 4, 0x1000⟩

theorem t_leImage_length : (leImage 0x1122 8).length = 8 := leImage_length _ _

theorem t_leValue_leImage :
    leValue (leImage 0x1122334455667788 8) = 0x1122334455667788 % 256 ^ 8 :=
  leValue_leImage _ _

theorem t_leImage_getElem? :
    (leImage 0x1122 8)[1]? = if 1 < 8 then some (UInt8.ofNat (0x1122 / 256 ^ 1)) else none :=
  leImage_getElem? _ _ _

theorem t_leValue_lt : leValue [0xFF, 0xFF] < 256 ^ ([0xFF, 0xFF] : List UInt8).length :=
  leValue_lt [0xFF, 0xFF]

theorem t_leImage_leValue :
    leImage (leValue [0x88, 0x77, 0x66, 0x55]) ([0x88, 0x77, 0x66, 0x55] : List UInt8).length =
      [0x88, 0x77, 0x66, 0x55] :=
  leImage_leValue [0x88, 0x77, 0x66, 0x55]

theorem t_encodePtrFragsAux_length : (encodePtrFragsAux 1 1 0 8 0 0 8).length = 8 :=
  encodePtrFragsAux_length _ _ _ _ _ _ _

theorem t_encodePtrFragsAux_getElem? :
    (encodePtrFragsAux 1 1 0 8 0 0 8)[3]? =
      if 3 < 8 then some (.init (UInt8.ofNat (0 / 256 ^ 3)) (some ⟨1, 1, 0 + 3, 0, 8⟩)) else none :=
  encodePtrFragsAux_getElem? _ _ _ _ _ _ _ _

theorem t_fragsCoherentFrom_encode :
    fragsCoherentFrom 1 1 0 8 0 (encodePtrFragsAux 1 1 0 8 0 0 8) = true :=
  fragsCoherentFrom_encode _ _ _ _ _ _ _

theorem t_dataBytesProto_encode :
    dataBytesProto (encodePtrFragsAux 3 7 0x1122 8 0x1122 0 8) = some (leImage 0x1122 8) :=
  dataBytesProto_encode _ _ _ _ _ _ _

theorem t_fragsCoherentFrom_getElem? :
    ∃ b, (encodePtrFragsAux 1 1 0 8 0 0 8)[2]?.getD .uninit =
      .init b (some ⟨1, 1, 0 + 2, 0, 8⟩) :=
  fragsCoherentFrom_getElem? 1 1 0 8 (encodePtrFragsAux 1 1 0 8 0 0 8) 0
    (fragsCoherentFrom_encode 1 1 0 8 0 0 8) 2 _ rfl

/-- Round trip of the all-zero 64-bit pointer (every byte `0x00`). -/
theorem t_roundtrip_zero_64 :
    abstractBytesCoherentPtrProvProto 8 (encodePtrBytesProto pZero 8) = some ⟨1, 1, 0⟩ :=
  (coherent_encode pZero 8 (by decide)).trans rfl

theorem t_roundtrip_big_32 :
    abstractBytesCoherentPtrProvProto 4 (encodePtrBytesProto pBig4 4) = some pBig4 :=
  (coherent_encode pBig4 4 (by decide)).trans rfl

theorem t_coherent_some_frags :
    (encodePtrBytesProto pZero 8).length = 8 ∧
    ∀ (i : Nat) (x : AbstractByteProto), (encodePtrBytesProto pZero 8)[i]? = some x →
      ∃ b, x = .init b (some ⟨1, 1, i, 0, 8⟩) :=
  coherent_some_frags 8 _ ⟨1, 1, 0⟩ t_roundtrip_zero_64

theorem t_dataBytesProto_length :
    (leImage 0x1122334455667788 8).length = (encodePtrBytesProto pBig 8).length :=
  dataBytesProto_length _ _ (dataBytesProto_encode _ _ _ _ _ _ _)

theorem t_dataBytesProto_getElem? :
    (leImage 0x1122 8)[1]? = some 0x11 :=
  dataBytesProto_getElem? (encodePtrBytesProto ⟨1, 1, 0x1122⟩ 8) (leImage 0x1122 8)
    (dataBytesProto_encode _ _ _ _ _ _ _) 1 0x11 _ rfl

/-- Exact algebraic characterization (`↔`) instantiated in both directions. -/
theorem t_coherent_iff_encode :
    (0 < 8 ∧ pTag.offsetBytes < 256 ^ 8 ∧ encodePtrBytesProto pTag 8 = encodePtrBytesProto pTag 8) ∧
    abstractBytesCoherentPtrProvProto 8 (encodePtrBytesProto pTag 8) = some pTag :=
  ⟨(coherent_iff_encode 8 _ pTag).mp ((coherent_encode pTag 8 (by decide)).trans rfl),
    (coherent_iff_encode 8 _ pTag).mpr ⟨by decide, by decide, rfl⟩⟩

/-- Exact `tag` preservation with `tag ≠ allocId` (live drops it, see `w3_tag_dropped`). -/
theorem t_exact_tag_64 :
    decodePtrBytesNoForgeProto true .thin 8 (encodePtrBytesProto pTag 8) = some (.ptr pTag 8) :=
  decode_encode_thin_exact true pTag 8 (by decide) (by decide)

theorem t_exact_tag_32_raw :
    decodePtrBytesNoForgeProto false .thin 4 (encodePtrBytesProto pBig4 4) = some (.ptr pBig4 4) :=
  decode_encode_thin_exact false pBig4 4 (by decide) (by decide)

/-- Un-normalized offset `2^64 + 5` decodes to its normalized offset `5`. -/
theorem t_unnormalized_offset :
    decodeThinPtrBytesProto true 8 (encodePtrBytesProto ⟨1, 1, 2 ^ 64 + 5⟩ 8) =
      some (.ptr ⟨1, 1, 5⟩ 8) :=
  (decodeThin_encode true _ 8 (by decide)).trans rfl

/-- `5` and `2^64 + 5` have identical images (Miri sees identical `bytes`): their splice is
an intact pointer, not a forgery. -/
theorem t_unnormalized_splice_kept :
    abstractBytesCoherentPtrProvProto 8
      (spliceBytes 1 (encodePtrBytesProto ⟨1, 1, 5⟩ 8) (encodePtrBytesProto ⟨1, 1, 2 ^ 64 + 5⟩ 8)) =
      some ⟨1, 1, 5⟩ := rfl

theorem t_none_byteIdx_ne :
    abstractBytesCoherentPtrProvProto 8 [.init 0 (some ⟨1, 1, 1, 0, 8⟩)] = none :=
  coherent_none_of_byteIdx_ne 8 _ 0 0 _ rfl (by decide)

theorem t_none_ptrBytes_ne :
    abstractBytesCoherentPtrProvProto 8 [.init 0 (some ⟨1, 1, 0, 0, 4⟩)] = none :=
  coherent_none_of_ptrBytes_ne 8 _ 0 0 _ rfl (by decide)

theorem t_none_no_frag : abstractBytesCoherentPtrProvProto 8 [.init 0 none] = none :=
  coherent_none_of_no_frag 8 _ 0 0 rfl

theorem t_none_uninit : abstractBytesCoherentPtrProvProto 8 [.uninit] = none :=
  coherent_none_of_uninit 8 _ 0 rfl

theorem t_none_frag_mismatch :
    abstractBytesCoherentPtrProvProto 2
      [.init 0 (some ⟨1, 1, 0, 0, 2⟩), .init 1 (some ⟨1, 1, 1, 256, 2⟩)] = none :=
  coherent_none_of_frag_mismatch 2 _ 0 1 _ _ _ _ rfl rfl (by decide)

theorem t_encode_getElem? :
    (encodePtrBytesProto pBig 8)[7]? =
      some (.init (UInt8.ofNat (normOffset 8 pBig.offsetBytes / 256 ^ 7))
        (some ⟨3, 7, 7, normOffset 8 pBig.offsetBytes, 8⟩)) :=
  encodePtrBytesProto_getElem? pBig 8 7 (by decide)

theorem t_encode_length : (encodePtrBytesProto pBig 8).length = 8 :=
  encodePtrBytesProto_length _ _

theorem t_moved_byte :
    abstractBytesCoherentPtrProvProto 8 ((encodePtrBytesProto pBig 8).set 0
      (.init (UInt8.ofNat (normOffset 8 pBig.offsetBytes / 256 ^ 5))
        (some ⟨3, 7, 5, normOffset 8 pBig.offsetBytes, 8⟩))) = none :=
  coherent_none_of_moved_byte pBig 8 _ 0 5 (by decide) (by decide) rfl

theorem t_two_le : ∃ m, 8 = m + 2 := two_le_iff_exists 8 (by decide)

/-- Byte reversal of the all-zero 64-bit pointer (byte-identical image) is stripped. -/
theorem t_reverse_zero_64 :
    abstractBytesCoherentPtrProvProto 8 (encodePtrBytesProto pZero 8).reverse = none :=
  coherent_reverse_none pZero 8 (by decide)

theorem t_reverse_32 :
    abstractBytesCoherentPtrProvProto 4 (encodePtrBytesProto pBig4 4).reverse = none :=
  coherent_reverse_none pBig4 4 (by decide)

theorem t_swap01 :
    abstractBytesCoherentPtrProvProto 8 (swapFirstTwo (encodePtrBytesProto pBig 8)) = none :=
  coherent_swap01_none pBig 8 (by decide)

theorem t_dup0 :
    abstractBytesCoherentPtrProvProto 8 (dupFirstByte (encodePtrBytesProto pZero 8)) = none :=
  coherent_dup_none pZero 8 (by decide)

/-- The reversal permutation `i ↦ 7 - i` given as an index map. -/
theorem t_permute :
    abstractBytesCoherentPtrProvProto 8
      (permuteBytes (fun i => 7 - i) (encodePtrBytesProto pZero 8)) = none :=
  coherent_permute_none pZero 8 (fun i => 7 - i) 0 (by decide) (by decide) (by decide)

/-- `UCG#558`: byte `0` of `p = 0` with bytes `1..7` of `p + 256` (identical byte `0`). -/
theorem t_splice_0_256 :
    abstractBytesCoherentPtrProvProto 8
      (spliceBytes 1 (encodePtrBytesProto pZero 8) (encodePtrBytesProto p256 8)) = none :=
  coherent_splice_none pZero p256 8 1 (by decide) (by decide) (by decide)

theorem t_splice_p_p4_32 :
    abstractBytesCoherentPtrProvProto 4
      (spliceBytes 1 (encodePtrBytesProto ⟨1, 1, 0x10⟩ 4) (encodePtrBytesProto ⟨1, 1, 0x14⟩ 4)) =
      none :=
  coherent_splice_none ⟨1, 1, 0x10⟩ ⟨1, 1, 0x14⟩ 4 1 (by decide) (by decide) (by decide)

theorem t_splice_mixed_alloc :
    abstractBytesCoherentPtrProvProto 8
      (spliceBytes 4 (encodePtrBytesProto ⟨1, 1, 0x10⟩ 8) (encodePtrBytesProto ⟨2, 1, 0x10⟩ 8)) =
      none :=
  coherent_splice_none ⟨1, 1, 0x10⟩ ⟨2, 1, 0x10⟩ 8 4 (by decide) (by decide) (by decide)

theorem t_splice_mixed_tag :
    abstractBytesCoherentPtrProvProto 8
      (spliceBytes 7 (encodePtrBytesProto ⟨1, 1, 0x10⟩ 8) (encodePtrBytesProto ⟨1, 2, 0x10⟩ 8)) =
      none :=
  coherent_splice_none ⟨1, 1, 0x10⟩ ⟨1, 2, 0x10⟩ 8 7 (by decide) (by decide) (by decide)

theorem t_set_plain :
    abstractBytesCoherentPtrProvProto 8 ((encodePtrBytesProto pBig 8).set 3 (.init 0x55 none)) =
      none :=
  coherent_set_plain_none pBig 8 3 0x55 (by decide)

theorem t_set_uninit :
    abstractBytesCoherentPtrProvProto 8 ((encodePtrBytesProto pBig 8).set 7 .uninit) = none :=
  coherent_set_uninit_none pBig 8 7 (by decide)

/-- Two 32-bit pointer images read as one 64-bit pointer. -/
theorem t_cross_width :
    abstractBytesCoherentPtrProvProto (4 + 4)
      (encodePtrBytesProto pBig4 4 ++ encodePtrBytesProto pBig4 4) = none :=
  coherent_cross_width_none pBig4 pBig4 4 (by decide)

theorem t_encode_normOffset :
    encodePtrBytesProto ⟨1, 1, 2 ^ 64 + 5⟩ 8 =
      encodePtrBytesProto ⟨1, 1, normOffset 8 (2 ^ 64 + 5)⟩ 8 :=
  encodePtrBytesProto_normOffset ⟨1, 1, 2 ^ 64 + 5⟩ 8

theorem t_splice_equiv_normOffset :
    abstractBytesCoherentPtrProvProto 8
      (spliceBytes 3 (encodePtrBytesProto ⟨5, 9, 5⟩ 8)
        (encodePtrBytesProto ⟨5, 9, 2 ^ 64 + 5⟩ 8)) =
      some ⟨5, 9, normOffset 8 5⟩ :=
  coherent_splice_equiv_normOffset ⟨5, 9, 5⟩ ⟨5, 9, 2 ^ 64 + 5⟩ 8 3 (by decide) rfl rfl rfl

theorem t_take_append : ([1, 2] ++ [3] : List Nat).take 2 = [1, 2] :=
  take_append_of_length _ _ 2 rfl

theorem t_drop_append : ([1, 2] ++ [3] : List Nat).drop 2 = [3] :=
  drop_append_of_length _ _ 2 rfl

theorem t_dyn_exact :
    decodePtrBytesNoForgeProto true .dyn 8 (encodePtrBytesProto pTag 8 ++ encodePtrBytesProto pVt 8) =
      some (.aggregate [.ptr pTag 8, .ptr pVt 8]) :=
  decode_encode_dyn_exact true pTag pVt 8 (by decide) (by decide) (by decide)

theorem t_dyn_exact_32_raw :
    decodePtrBytesNoForgeProto false .dyn 4
      (encodePtrBytesProto pBig4 4 ++ encodePtrBytesProto pVt 4) =
      some (.aggregate [.ptr pBig4 4, .ptr pVt 4]) :=
  decode_encode_dyn_exact false pBig4 pVt 4 (by decide) (by decide) (by decide)

theorem t_dataBytes_plain : dataBytesProto (encodeLittleEndianBytesProto 3 8) = some (leImage 3 8) :=
  dataBytesProto_plain _ _

theorem t_haveFrag_plain : abstractBytesHaveFragProto (encodeLittleEndianBytesProto 3 8) = false :=
  haveFrag_plain _ _

theorem t_plain_length : (encodeLittleEndianBytesProto 3 8).length = 8 := plain_length _ _

theorem t_slice_exact :
    decodePtrBytesNoForgeProto true .slice 8
      (encodePtrBytesProto pTag 8 ++ encodeLittleEndianBytesProto 3 8) =
      some (.aggregate [.ptr pTag 8, .scalar 3 8]) :=
  decode_encode_slice_exact true pTag 3 8 (by decide) (by decide) (by decide)

theorem t_str_exact :
    decodePtrBytesNoForgeProto true .str 8
      (encodePtrBytesProto pTag 8 ++ encodeLittleEndianBytesProto 5 8) =
      some (.aggregate [.ptr pTag 8, .scalar 5 8]) :=
  decode_encode_str_exact true pTag 5 8 (by decide) (by decide) (by decide)

theorem t_thin_unnormalized :
    decodePtrBytesNoForgeProto true .thin 4 (encodePtrBytesProto ⟨5, 9, 2 ^ 32 + 7⟩ 4) =
      some (.ptr ⟨5, 9, normOffset 4 (2 ^ 32 + 7)⟩ 4) :=
  decode_encode_thin_unnormalized true ⟨5, 9, 2 ^ 32 + 7⟩ 4 (by decide)

theorem t_haveFrag_some :
    abstractBytesHaveFragProto [mkInitByte 0, mkPtrFragByte 1 2 3 0 1 8] = true :=
  haveFrag_of_getElem?_some _ 1 1 ⟨2, 3, 0, 1, 8⟩ rfl

theorem t_dyn_rev_vtable_univ :
    decodePtrBytesNoForgeProto true .dyn 8
        (encodePtrBytesProto pTag 8 ++ (encodePtrBytesProto pVt 8).reverse) = none ∧
    ∃ vbits, decodePtrBytesNoForgeProto false .dyn 8
        (encodePtrBytesProto pTag 8 ++ (encodePtrBytesProto pVt 8).reverse) =
      some (.aggregate [.ptr pTag 8, .scalar vbits 8]) :=
  decode_dyn_rev_vtable_ref_none_raw_scalar pTag pVt 8 (by decide) (by decide)

theorem t_slice_prov_meta_none :
    decodePtrBytesNoForgeProto false .slice 8
        (encodePtrBytesProto pTag 8 ++ encodePtrBytesProto pVt 8) = none ∧
    decodePtrBytesNoForgeProto false .str 8
        (encodePtrBytesProto pTag 8 ++ encodePtrBytesProto pVt 8) = none :=
  decode_slice_prov_meta_none false (encodePtrBytesProto pTag 8) (encodePtrBytesProto pVt 8)
    8 0 _ _ (encodePtrBytesProto_length _ _) (encodePtrBytesProto_getElem? pVt 8 0 (by decide))

theorem t_slice_swapped_halves_none :
    decodePtrBytesNoForgeProto true .slice 8
        (encodeLittleEndianBytesProto 3 8 ++ encodePtrBytesProto pTag 8) = none ∧
    decodePtrBytesNoForgeProto true .str 8
        (encodeLittleEndianBytesProto 3 8 ++ encodePtrBytesProto pTag 8) = none :=
  decode_slice_swapped_halves_none true pTag 3 8 (by decide)

theorem t_dataBytes_append :
    dataBytesProto ([mkInitByte 1] ++ [mkInitByte 2]) = some ([1] ++ [2]) :=
  dataBytesProto_append _ _ _ _ rfl rfl

theorem t_dataBytes_reverse :
    dataBytesProto [mkInitByte 1, mkInitByte 2].reverse = some [1, 2].reverse :=
  dataBytesProto_reverse _ _ rfl

theorem t_reverse_ref_none_raw_scalar :
    decodePtrBytesNoForgeProto true .thin 8 (encodePtrBytesProto pZero 8).reverse = none ∧
    ∃ bits, decodePtrBytesNoForgeProto false .thin 8 (encodePtrBytesProto pZero 8).reverse =
      some (.scalar bits 8) :=
  decode_reverse_ref_none_raw_scalar pZero 8 (by decide)

theorem t_toProto_toOpt2 : (mkPtrFragByte 0 1 1 0 0 8).toOpt2.toProto = mkPtrFragByte 0 1 1 0 0 8 :=
  toProto_toOpt2 _

theorem t_toOpt2_map :
    ((encodePtrBytesProto pBig 8).map AbstractByteProto.toOpt2).map AbstractByteOpt2.toProto =
      encodePtrBytesProto pBig 8 :=
  toOpt2_map_toProto _

theorem t_coherentOpt2 :
    abstractBytesCoherentPtrProvOpt2 8 ((encodePtrBytesProto pBig 8).map AbstractByteProto.toOpt2) =
      some pBig :=
  (coherentOpt2_toOpt2 8 _).trans ((coherent_encode pBig 8 (by decide)).trans rfl)

theorem t_opt2_plain : (AbstractByteOpt2.init 7 none).toProto = mkInitByte 7 := opt2_plain_toProto 7

/-- An unmigrated Option 2 call site `.init b (some (a, t))` (no fragment) fails closed. -/
theorem t_opt2_unmigrated_fails_closed :
    abstractBytesCoherentPtrProvOpt2 8
      (List.replicate 8 (AbstractByteOpt2.init 0 (some (1, 1)))) = none :=
  coherentOpt2_none_of_missing_frag 8 _ 0 0 (some (1, 1)) rfl

/-- An incoherent Option 2 byte `.init b none (some m)` (orphan fragment) also fails closed. -/
theorem t_opt2_orphan_frag_fails_closed :
    abstractBytesCoherentPtrProvOpt2 8
      (List.replicate 8 (AbstractByteOpt2.init 0 none (some ⟨0, 0, 8⟩))) = none :=
  coherentOpt2_none_of_orphan_frag 8 _ 0 0 ⟨0, 0, 8⟩ rfl

theorem t_provPair : provPair? (mkPtrFragByte 0 5 9 0 0x40 8) = some (5, 9) :=
  provPair_mkPtrFragByte _ _ _ _ _ _

theorem t_opt2_hazard :
    opt2LegacyHasProv (.init 0 (some (1, 1))) = true ∧
    opt2LegacyHasProv (.init 0 (some (1, 1)) (some ⟨0, 0, 8⟩)) = false :=
  opt2_legacy_pattern_hazard

/-- Non-trivial injectivity instantiation: `5` and `2^64 + 5` share identical 8-byte images. -/
theorem t_imageVec8_inj : 5 % 256 ^ 8 = (2 ^ 64 + 5) % 256 ^ 8 :=
  imageVec8_inj 5 (2 ^ 64 + 5) rfl

theorem t_uint8_ofNat_toNat : (UInt8.ofNat 7).toNat = 7 := uint8_ofNat_toNat_of_lt 7 (by decide)

theorem t_miri_of_coherent :
    inspectFragmentsMirror none ((encodePtrBytesProto pBig 8).map toMiriFrag) =
      .ok (some (3, 7)) :=
  miri_of_coherent 8 (by decide) _ pBig ((coherent_encode pBig 8 (by decide)).trans rfl)

theorem t_miri_of_coherent_32 :
    inspectFragmentsMirror none ((encodePtrBytesProto pBig4 4).map toMiriFrag) =
      .ok (some (3, 7)) :=
  miri_of_coherent 4 (by decide) _ pBig4 ((coherent_encode pBig4 4 (by decide)).trans rfl)

/-- Non-empty instantiation of `miri_loop_of_frags` on a real 8-byte encoded pointer. -/
theorem t_miri_loop_of_frags :
    inspectFragmentsMirrorLoop none 0 (some ((3, 7), imageVec8 pBig.offsetBytes))
      ((encodePtrBytesProto pBig 8).map toMiriFrag) = .ok (some (3, 7)) :=
  miri_loop_of_frags 3 7 pBig.offsetBytes 8 (by decide) (encodePtrBytesProto pBig 8) 0
    (fun i x hx => by
      obtain ⟨_, hall⟩ := coherent_some_frags 8 _ pBig ((coherent_encode pBig 8 (by decide)).trans rfl)
      obtain ⟨b, hb⟩ := hall i x hx
      exact ⟨b, by simpa [pBig] using hb⟩)
    (by decide)

theorem t_fragsWellFormed : FragsWellFormed 8 (encodePtrBytesProto pBig 8) :=
  fragsWellFormed_encode pBig 8 (by decide)

/-- Non-empty instantiation of `miri_loop_inv` on a real 8-byte encoded pointer. -/
theorem t_miri_loop_inv :
    (3, 7) = (3, 7) ∧ ∀ (i : Nat) (x : AbstractByteProto), (encodePtrBytesProto pBig 8)[i]? = some x →
      ∃ b f, x = .init b (some f) ∧ (UInt8.ofNat f.byteIdx).toNat = 0 + i ∧ f.allocId = 3 ∧
        f.tag = 7 ∧ imageVec8 (normOffset f.ptrBytes f.origOffset) = imageVec8 pBig.offsetBytes :=
  miri_loop_inv 3 7 (imageVec8 pBig.offsetBytes) (encodePtrBytesProto pBig 8) 0 (3, 7)
    t_miri_loop_of_frags

/-- Miri ⇒ prototype on a real 64-bit and a real 32-bit image. -/
theorem t_coherent_of_miri :
    ∃ o, o < 256 ^ 8 ∧ encodePtrBytesProto pBig 8 = encodePtrBytesProto ⟨3, 7, o⟩ 8 ∧
      abstractBytesCoherentPtrProvProto 8 (encodePtrBytesProto pBig 8) = some ⟨3, 7, o⟩ :=
  coherent_of_miri 8 (by decide) (by decide) _ (encodePtrBytesProto_length _ _)
    (fragsWellFormed_encode _ 8 (by decide)) (3, 7) t_miri_of_coherent

theorem t_coherent_of_miri_32 :
    ∃ o, o < 256 ^ 4 ∧ encodePtrBytesProto pBig4 4 = encodePtrBytesProto ⟨3, 7, o⟩ 4 ∧
      abstractBytesCoherentPtrProvProto 4 (encodePtrBytesProto pBig4 4) = some ⟨3, 7, o⟩ :=
  coherent_of_miri 4 (by decide) (by decide) _ (encodePtrBytesProto_length _ _)
    (fragsWellFormed_encode _ 4 (by decide)) (3, 7) t_miri_of_coherent_32

theorem t_miri_loop_some_expected_ok :
    ∃ r, inspectFragmentsMirrorLoop none 0 (some ((3, 7), imageVec8 pBig.offsetBytes))
      ((encodePtrBytesProto pBig 8).map toMiriFrag) = .ok r :=
  miri_loop_some_expected_ok _ (encodePtrBytesProto pBig 8) 0

theorem t_miri_nonempty_ok :
    ∃ r, inspectFragmentsMirror none ((encodePtrBytesProto pBig 8).reverse.map toMiriFrag) = .ok r :=
  miri_nonempty_ok _ (by decide)

/-- Exact Proto ↔ Miri recovery biconditional (64-bit and 32-bit). -/
theorem t_coherent_iff_miri_some :
    inspectFragmentsMirror none ((encodePtrBytesProto pBig 8).map toMiriFrag) = .ok (some (3, 7)) ∧
    (abstractBytesCoherentPtrProvProto 4 (encodePtrBytesProto pBig4 4)).map
      (fun p => (p.allocId, p.tag)) = some (3, 7) :=
  ⟨(coherent_iff_miri_some 8 (by decide) (by decide) _ (encodePtrBytesProto_length _ _)
      (fragsWellFormed_encode _ 8 (by decide)) (3, 7)).mp rfl,
    (coherent_iff_miri_some 4 (by decide) (by decide) _ (encodePtrBytesProto_length _ _)
      (fragsWellFormed_encode _ 4 (by decide)) (3, 7)).mpr t_miri_of_coherent_32⟩

/-- Exact Proto ↔ Miri stripping biconditional on `p` / `p + 256` splice. -/
theorem t_coherent_iff_miri_none :
    inspectFragmentsMirror none
      ((spliceBytes 1 (encodePtrBytesProto pZero 8) (encodePtrBytesProto p256 8)).map toMiriFrag) =
      .ok none :=
  (coherent_iff_miri_none 8 (by decide) (by decide) _ rfl
    (fragsWellFormed_splice 8 1 _ _ (by decide) (fragsWellFormed_encode _ 8 (by decide))
      (fragsWellFormed_encode _ 8 (by decide)))).mp t_splice_0_256

theorem t_toMiniRust_encodeAux :
    (encodePtrFragsAux 1 1 0 8 0 0 8).map AbstractByteProto.toMiniRust =
      MiniRustSpec.Interp.encodePtrBytes (some (mrProv 1)) 0 (leImage 0 8) :=
  toMiniRust_encodeAux _ _ _ _ _ _ _

/-- The prototype encoding is exactly live MiniRust's `encode_ptr` image (tag erased). -/
theorem t_toMiniRust_encode :
    (encodePtrBytesProto pBig 8).map AbstractByteProto.toMiniRust = mrEnc 3 0x1122334455667788 :=
  (toMiniRust_encode pBig 8).trans rfl

/-- Non-empty instantiation of `mr_keep` on a real 8-byte encoded pointer. -/
theorem t_mr_keep :
    MiniRustSpec.Interp.decodePtrProvenance 0 (some (mrProv 3))
      ((encodePtrBytesProto pBig 8).map AbstractByteProto.toMiniRust) = some (mrProv 3) :=
  mr_keep 3 (encodePtrBytesProto pBig 8) 0 (fun i x hx => by
    obtain ⟨_, hall⟩ := coherent_some_frags 8 _ pBig ((coherent_encode pBig 8 (by decide)).trans rfl)
    obtain ⟨b, hb⟩ := hall i x hx
    exact ⟨b, _, hb, rfl, (Nat.zero_add i).symm⟩)

theorem t_mr_of_coherent :
    mrDecodedProv ((encodePtrBytesProto pBig 8).map AbstractByteProto.toMiniRust) =
      some (mrProv 3) :=
  mr_of_coherent 8 _ pBig ((coherent_encode pBig 8 (by decide)).trans rfl)

theorem t_mr_none_acc : MiniRustSpec.Interp.decodePtrProvenance 0 none (mrEnc 1 5) = none :=
  mr_none_acc _ _

theorem t_mr_strip :
    MiniRustSpec.Interp.decodePtrProvenance 0 none
      ([mkInitByte 0].map AbstractByteProto.toMiniRust) = none :=
  mr_strip (mrProv 0) _ 0 none 0 _ (Or.inr rfl) rfl (fun _ h => by
    simp [mkInitByte, AbstractByteProto.toMiniRust,
      MiniRustSpec.Interp.AbstractByte.provenance_frag] at h)

theorem t_mr_strip_top : mrDecodedProv ([AbstractByteProto.uninit].map AbstractByteProto.toMiniRust) =
    none :=
  mr_strip_top _ 0 _ rfl (fun _ _ h => by
    simp [AbstractByteProto.toMiniRust, MiniRustSpec.Interp.AbstractByte.provenance_frag] at h)

/-- 3-way agreement on the byte-reversed 64-bit pointer: byte `0` carries fragment `7`. -/
theorem t_agree_moved :
    abstractBytesCoherentPtrProvProto 8 (encodePtrBytesProto pBig 8).reverse = none ∧
      mrDecodedProv ((encodePtrBytesProto pBig 8).reverse.map AbstractByteProto.toMiniRust) = none :=
  agree_strip_moved 8 _ 0 _ ⟨3, 7, 7, normOffset 8 pBig.offsetBytes, 8⟩ rfl (by decide)

theorem t_agree_plain :
    abstractBytesCoherentPtrProvProto 8 ((encodePtrBytesProto pBig 8).set 2 (mkInitByte 0)) = none ∧
      mrDecodedProv (((encodePtrBytesProto pBig 8).set 2 (mkInitByte 0)).map
        AbstractByteProto.toMiniRust) = none :=
  agree_strip_plain 8 _ 2 0 rfl

theorem t_agree_mixed_alloc :
    abstractBytesCoherentPtrProvProto 8
        (spliceBytes 4 (encodePtrBytesProto ⟨1, 1, 0x10⟩ 8) (encodePtrBytesProto ⟨2, 1, 0x10⟩ 8)) =
      none ∧
    mrDecodedProv ((spliceBytes 4 (encodePtrBytesProto ⟨1, 1, 0x10⟩ 8)
      (encodePtrBytesProto ⟨2, 1, 0x10⟩ 8)).map AbstractByteProto.toMiniRust) = none :=
  agree_strip_mixed_alloc 8 _ 0 4 _ _ ⟨1, 1, 0, 0x10, 8⟩ ⟨2, 1, 4, 0x10, 8⟩ rfl rfl (by decide)

theorem t_splice_getElem? :
    (spliceBytes 1 [1, 2, 3] [4, 5, 6])[2]? = if 2 < 1 then [1, 2, 3][2]? else [4, 5, 6][2]? :=
  spliceBytes_getElem? 1 [1, 2, 3] [4, 5, 6] (by decide) 2

/-- **Strict refinement (`UCG#558`):** MiniRust keeps the `p` / `p + 256` splice; the
prototype strips it (`t_splice_0_256`). -/
theorem t_mr_keeps_splice_0_256 :
    mrDecodedProv ((spliceBytes 1 (encodePtrBytesProto pZero 8) (encodePtrBytesProto p256 8)).map
      AbstractByteProto.toMiniRust) = some (mrProv 1) :=
  mr_keeps_same_alloc_splice pZero p256 8 1 (by decide) (by decide) rfl

theorem t_mr_keeps_tag_splice :
    mrDecodedProv ((spliceBytes 4 (encodePtrBytesProto ⟨1, 1, 0x10⟩ 8)
      (encodePtrBytesProto ⟨1, 2, 0x10⟩ 8)).map AbstractByteProto.toMiniRust) = some (mrProv 1) :=
  mr_keeps_same_alloc_splice _ _ 8 4 (by decide) (by decide) rfl

theorem t_agree_uninit :
    abstractBytesCoherentPtrProvProto 8 ((encodePtrBytesProto pBig 8).set 5 .uninit) = none ∧
      mrDecodedProv (((encodePtrBytesProto pBig 8).set 5 .uninit).map AbstractByteProto.toMiniRust) =
        none :=
  agree_strip_uninit 8 _ 5 rfl

theorem t_mr_leValue_eq : MiniRustSpec.Interp.leValue [0x22, 0x11] = leValue [0x22, 0x11] :=
  mr_leValue_eq [0x22, 0x11]

theorem t_mr_mapM_data :
    ((encodePtrBytesProto pBig 8).map AbstractByteProto.toMiniRust).mapM
        MiniRustSpec.Interp.AbstractByte.data = some (leImage pBig.offsetBytes 8) :=
  mr_mapM_data_of_dataBytesProto _ _ (dataBytesProto_encode _ _ _ _ _ _ _)

theorem t_mr_decodePtr_coherent_8 :
    MiniRustSpec.Interp.decodePtr ((encodePtrBytesProto pBig 8).map AbstractByteProto.toMiniRust) =
      .ok (some { addr := (pBig.offsetBytes : Int), provenance := some (mrProv 3) }) :=
  mr_decodePtr_of_coherent_8 _ pBig ((coherent_encode pBig 8 (by decide)).trans rfl)

theorem t_mr_decodePtr_reverse_8 :
    MiniRustSpec.Interp.decodePtr
        ((encodePtrBytesProto pBig 8).reverse.map AbstractByteProto.toMiniRust) =
      .ok (some { addr := (leValue (leImage (normOffset 8 pBig.offsetBytes) 8).reverse : Int),
                  provenance := none }) :=
  mr_decodePtr_reverse_8 pBig

theorem t_dataBytesProto_take :
    dataBytesProto ((encodePtrBytesProto pBig 8).take 3) =
      some ((leImage pBig.offsetBytes 8).take 3) :=
  dataBytesProto_take _ _ 3 (dataBytesProto_encode _ _ _ _ _ _ _)

theorem t_dataBytesProto_drop :
    dataBytesProto ((encodePtrBytesProto pBig 8).drop 3) =
      some ((leImage pBig.offsetBytes 8).drop 3) :=
  dataBytesProto_drop _ _ 3 (dataBytesProto_encode _ _ _ _ _ _ _)

theorem t_fragsWellFormed_splice :
    FragsWellFormed 8 (spliceBytes 1 (encodePtrBytesProto pZero 8) (encodePtrBytesProto p256 8)) :=
  fragsWellFormed_splice 8 1 _ _ (by decide) (fragsWellFormed_encode _ 8 (by decide))
    (fragsWellFormed_encode _ 8 (by decide))

/-- Universal 3-way `UCG#558` strict-refinement theorem instantiated on `p = 0` vs `p + 256`. -/
theorem t_mr_decodePtr_splice_8_strict :
    let spliced := spliceBytes 1 (encodePtrBytesProto pZero 8) (encodePtrBytesProto p256 8)
    abstractBytesCoherentPtrProvProto 8 spliced = none ∧
    inspectFragmentsMirror none (spliced.map toMiriFrag) = .ok none ∧
    ∃ addr, MiniRustSpec.Interp.decodePtr (spliced.map AbstractByteProto.toMiniRust) =
      .ok (some { addr := addr, provenance := some (mrProv 1) }) :=
  mr_decodePtr_splice_8_strict_refinement pZero p256 1 (by decide) (by decide) rfl (by decide)

theorem t_copyBytewise_eq :
    copyBytewiseProto [mkInitByte 1] [AbstractByteProto.uninit] = [mkInitByte 1] :=
  copyBytewise_eq _ _ rfl

/-- In-order byte-by-byte copy of a 64-bit pointer into `[MaybeUninit<u8>; 8]`. -/
theorem t_copyBytewise_ptr :
    copyBytewiseProto (encodePtrBytesProto pTag 8) (List.replicate 8 .uninit) =
        encodePtrBytesProto pTag 8 ∧
    decodePtrBytesNoForgeProto true .thin 8
        (copyBytewiseProto (encodePtrBytesProto pTag 8) (List.replicate 8 .uninit)) =
      some (.ptr pTag 8) :=
  copyBytewise_preserves_ptr true pTag 8 (by decide) (by decide) _ rfl

theorem t_copyBytewise_ptr_32 :
    copyBytewiseProto (encodePtrBytesProto pBig4 4) (List.replicate 4 (mkInitByte 0)) =
        encodePtrBytesProto pBig4 4 ∧
    decodePtrBytesNoForgeProto false .thin 4
        (copyBytewiseProto (encodePtrBytesProto pBig4 4) (List.replicate 4 (mkInitByte 0))) =
      some (.ptr pBig4 4) :=
  copyBytewise_preserves_ptr false pBig4 4 (by decide) (by decide) _ rfl

theorem t_copyNonOverlapping_ptr :
    copyNonOverlappingBytesProto (encodePtrBytesProto pTag 8) (List.replicate 8 .uninit) 0 0 8 =
      some (encodePtrBytesProto pTag 8) ∧
    decodePtrBytesNoForgeProto true .thin 8 (encodePtrBytesProto pTag 8) = some (.ptr pTag 8) :=
  copyNonOverlapping_preserves_ptr true pTag 8 (by decide) (by decide) _ rfl

theorem t_write_inBounds :
    writeBytesProto [.uninit] 0 [mkInitByte 2] =
      some (([AbstractByteProto.uninit].take 0) ++ [mkInitByte 2] ++
        [AbstractByteProto.uninit].drop (0 + [mkInitByte 2].length)) :=
  writeBytesProto_inBounds _ _ _ (by decide)

theorem t_copy_inBounds :
    copyNonOverlappingBytesProto [mkInitByte 2] [.uninit] 0 0 1 =
      some ([AbstractByteProto.uninit].take 0 ++ ([mkInitByte 2].drop 0).take 1 ++
        [AbstractByteProto.uninit].drop (0 + (([mkInitByte 2].drop 0).take 1).length)) :=
  copyNonOverlappingBytesProto_inBounds _ _ _ _ _ (by decide) (by decide)

theorem t_fill_inBounds :
    writeBytesFillProto [.uninit] 0 2 1 =
      some ([AbstractByteProto.uninit].take 0 ++ List.replicate 1 (mkInitByte 2) ++
        [AbstractByteProto.uninit].drop (0 + 1)) :=
  writeBytesFillProto_inBounds _ _ _ _ (by decide)

theorem t_decodePlainInt_byte : decodePlainIntProto 1 [mkInitByte 2] = some (.scalar 2 1) :=
  decodePlainInt_byte 2

theorem t_readBool_byte :
    decodeTypedValueFromBytesProto 8 .bool [mkInitByte 1] =
      match Nat.ble (1 : UInt8).toNat 1 with
      | true => some (.scalar (1 : UInt8).toNat 1)
      | false => none :=
  readBool_byte 8 1

theorem t_ble_false : Nat.ble 2 1 = false := ble_one_false_of_two_le 2 (by decide)

theorem t_readBool_2_none : decodeTypedValueFromBytesProto 8 .bool [mkInitByte 2] = none :=
  readBool_invalid_none 8 2 (by decide)

theorem t_readUnalignedBool_2_none :
    decodeTypedValueFromBytesProto 8 (.unaligned .bool) [mkInitByte 2] = none :=
  readUnalignedBool_invalid_none 8 2 (by decide)

theorem t_readMaybeUninit_2 :
    decodeTypedValueFromBytesProto 8 (.maybeUninit .bool) [mkInitByte 2] =
      some (.rawBytes [mkInitByte 2]) :=
  readMaybeUninit_any 8 .bool _ rfl

theorem t_readMaybeUninit_uninit :
    decodeTypedValueFromBytesProto 8 (.maybeUninit (.unaligned .bool)) [.uninit] =
      some (.rawBytes [.uninit]) :=
  readMaybeUninit_any 8 _ _ rfl

theorem t_readU8_2 : decodeTypedValueFromBytesProto 8 (.uint 1) [mkInitByte 2] = some (.scalar 2 1) :=
  readU8_byte 8 2

/-- Fragment-preserving union raw-byte overlay keeps `tag ≠ allocId` intact across round-trip. -/
theorem t_rawOverlay_roundtrip_ptr :
    decodeRawOverlayProto (encodeRawOverlayProto (encodePtrBytesProto pTag 8)) =
      some (encodePtrBytesProto pTag 8) ∧
    decodePtrBytesNoForgeProto true .thin 8 (encodePtrBytesProto pTag 8) = some (.ptr pTag 8) :=
  rawOverlay_roundtrip_ptr true pTag 8 (by decide) (by decide)

theorem t_readBytes_writeBytes :
    readBytesProto ([AbstractByteProto.uninit, .uninit].take 1 ++ [mkInitByte 2] ++
      [AbstractByteProto.uninit, .uninit].drop (1 + [mkInitByte 2].length)) 1
      [mkInitByte 2].length = some [mkInitByte 2] :=
  readBytesProto_writeBytesProto [.uninit, .uninit] 1 [mkInitByte 2] (by decide)

theorem t_readUnalignedBool_at_offset_chain :
    ∃ buf₁ buf₂,
      writeBytesProto [mkInitByte 7, .uninit, mkInitByte 9, mkInitByte 9] 1 [mkInitByte 2] =
        some buf₁ ∧
      readTypedFromBytesProto 8 (.uint 1) buf₁ 1 = some (.scalar 2 1) ∧
      readTypedFromBytesProto 8 .bool buf₁ 1 = none ∧
      readTypedFromBytesProto 8 (.unaligned .bool) buf₁ 1 = none ∧
      writeBytesProto buf₁ 1 [mkInitByte 1] = some buf₂ ∧
      readTypedFromBytesProto 8 .bool buf₂ 1 = some (.scalar 1 1) ∧
      readTypedFromBytesProto 8 (.unaligned .bool) buf₂ 1 = some (.aggregate [.scalar 1 1]) :=
  readUnalignedBool_at_offset_chain 8 [mkInitByte 7, .uninit, mkInitByte 9, mkInitByte 9] 1 2 1
    (by decide) (by decide) (by decide)

theorem t_isValidCharCode_surrogate_false :
    Trusted.Rustc.V2026_06_01.MirSemantics.isValidCharCode 0xD800 = false :=
  isValidCharCode_surrogate_false 0xD800 (by decide) (by decide)

theorem t_write_and_read_char_surrogate_univ :
    ∃ buf₁,
      writeBytesProto (List.replicate 6 .uninit) 1 (encodeLittleEndianBytesProto 0xDFFF 4) =
        some buf₁ ∧
      readTypedFromBytesProto 8 .char buf₁ 1 = none ∧
      readTypedFromBytesProto 8 (.uint 4) buf₁ 1 = some (.scalar 0xDFFF 4) :=
  write_and_read_char_surrogate_univ 8 (List.replicate 6 .uninit) 1 0xDFFF
    (by decide) (by decide) (by decide)

theorem t_kani_nested_maybeUninit_unaligned_bool_univ :
    copyNonOverlappingBytesProto [mkInitByte 2] [.uninit] 0 0 1 = some [mkInitByte 2] ∧
    readTypedFromBytesProto 8 (.maybeUninit (.maybeUninit (.unaligned .bool)))
        [mkInitByte 2] 0 = some (.rawBytes [mkInitByte 2]) ∧
    readTypedFromBytesProto 8 (.maybeUninit (.unaligned .bool))
        [mkInitByte 2] 0 = some (.rawBytes [mkInitByte 2]) ∧
    readTypedFromBytesProto 8 (.unaligned .bool) [mkInitByte 2] 0 = none ∧
    readTypedFromBytesProto 8 .bool [mkInitByte 2] 0 = none :=
  kani_nested_maybeUninit_unaligned_bool_univ 8 2 (by decide)

theorem t_toLive06_encodeAux :
    (encodePtrFragsAux 1 1 0 8 0 0 8).map AbstractByteProto.toLive06 =
      Trusted.Rustc.V2026_06_01.MirSemantics.encodeLittleEndianBytes 0 8 (some (1, 1)) :=
  toLive06_encodeAux _ _ _ _ _ _ _

theorem t_toLive08_encodeAux :
    (encodePtrFragsAux 1 1 0 8 0 0 8).map AbstractByteProto.toLive08 =
      Trusted.Rustc.V2026_08_01.MirSemantics.encodeLittleEndianBytes 0 8 (some (1, 1)) :=
  toLive08_encodeAux _ _ _ _ _ _ _

theorem t_toLive06_encode :
    (encodePtrBytesProto pBig 8).map AbstractByteProto.toLive06 =
      LiveV06.liveEnc 3 7 0x1122334455667788 8 :=
  (toLive06_encode pBig 8).trans rfl

theorem t_toLive08_encode :
    (encodePtrBytesProto pBig 8).map AbstractByteProto.toLive08 =
      LiveV08.liveEnc 3 7 0x1122334455667788 8 :=
  (toLive08_encode pBig 8).trans rfl

theorem t_ite_pos : (if 1 < 2 then 3 else 4) = 3 := ite_pos' (by decide)
theorem t_ite_neg : (if 2 < 1 then 3 else 4) = 4 := ite_neg' (by decide)

theorem t_decode_plain_no_forge :
    decodeTypedValueFromBytesProto 8 (.rawPtr .thin) (encodeLittleEndianBytesProto 0x20004 8) =
      some (.scalar 0x20004 8) ∧
    decodeTypedValueFromBytesProto 8 (.ref .thin) (encodeLittleEndianBytesProto 0x20004 8) = none ∧
    decodeTypedValueFromBytesProto 8 .fnPtr (encodeLittleEndianBytesProto 0x20004 8) = none :=
  decode_plain_no_forge 0x20004 8 (by decide) (by decide)

theorem t_decode_plain_no_forge_32 :
    decodeTypedValueFromBytesProto 4 (.rawPtr .thin) (encodeLittleEndianBytesProto 0 4) =
      some (.scalar 0 4) ∧
    decodeTypedValueFromBytesProto 4 (.ref .thin) (encodeLittleEndianBytesProto 0 4) = none ∧
    decodeTypedValueFromBytesProto 4 .fnPtr (encodeLittleEndianBytesProto 0 4) = none :=
  decode_plain_no_forge 0 4 (by decide) (by decide)

theorem t_decode_ptr_as_int_none :
    decodeTypedValueFromBytesProto 8 (.uint 8) (encodePtrBytesProto pTag 8) = none :=
  decode_ptr_as_int_none pTag 8 (by decide)

theorem t_decode_ptr_as_int_none_32 :
    decodeTypedValueFromBytesProto 4 (.uint 4) (encodePtrBytesProto pBig4 4) = none :=
  decode_ptr_as_int_none pBig4 4 (by decide)

theorem t_decode_plain_wide_no_forge :
    let bs := encodeLittleEndianBytesProto 0x20004 8 ++ encodeLittleEndianBytesProto 7 8
    decodeTypedValueFromBytesProto 8 (.ref .slice) bs = none ∧
    decodeTypedValueFromBytesProto 8 (.ref .str) bs = none ∧
    decodeTypedValueFromBytesProto 8 (.ref .dyn) bs = none ∧
    decodeTypedValueFromBytesProto 8 (.rawPtr .slice) bs =
      some (.aggregate [.scalar 0x20004 8, .scalar 7 8]) ∧
    decodeTypedValueFromBytesProto 8 (.rawPtr .str) bs =
      some (.aggregate [.scalar 0x20004 8, .scalar 7 8]) ∧
    decodeTypedValueFromBytesProto 8 (.rawPtr .dyn) bs =
      some (.aggregate [.scalar 0x20004 8, .scalar 7 8]) :=
  decode_plain_wide_no_forge 0x20004 7 8 (by decide) (by decide) (by decide)

theorem t_decode_ptr_subslice_as_int_none :
    readTypedFromBytesProto 8 (.uint 1) (encodePtrBytesProto pTag 8) 3 = none ∧
    readTypedFromBytesProto 8 (.maybeUninit (.uint 1)) (encodePtrBytesProto pTag 8) 3 =
      some (.rawBytes (((encodePtrBytesProto pTag 8).drop 3).take 1)) :=
  decode_ptr_subslice_as_int_none pTag 8 3 1 (by decide) (by decide)

theorem t_nat_blt_eq_true : Nat.blt 3 8 = true := nat_blt_eq_true_of_lt (by decide)

theorem t_typed_encode_decode_roundtrip :
    (encodeValueToBytesProto 8 (.uint 8) (.scalar 0x1234 8)).bind
        (decodeTypedValueFromBytesProto 8 (.uint 8)) = some (.scalar 0x1234 8) ∧
    (encodeValueToBytesProto 8 .bool (.scalar (1 : UInt8).toNat 1)).bind
        (decodeTypedValueFromBytesProto 8 .bool) = some (.scalar (1 : UInt8).toNat 1) ∧
    (encodeValueToBytesProto 8 .char (.scalar 0x41 4)).bind
        (decodeTypedValueFromBytesProto 8 .char) = some (.scalar 0x41 4) ∧
    (encodeValueToBytesProto 8 (.ref .thin) (.ptr pTag 8)).bind
        (decodeTypedValueFromBytesProto 8 (.ref .thin)) = some (.ptr pTag 8) ∧
    (encodeValueToBytesProto 8 .fnPtr (.ptr pTag 8)).bind
        (decodeTypedValueFromBytesProto 8 .fnPtr) = some (.ptr pTag 8) ∧
    (encodeValueToBytesProto 8 (.ref .dyn) (.aggregate [.ptr pTag 8, .ptr pVt 8])).bind
        (decodeTypedValueFromBytesProto 8 (.ref .dyn)) = some (.aggregate [.ptr pTag 8, .ptr pVt 8]) ∧
    (encodeValueToBytesProto 8 (.ref .slice) (.aggregate [.ptr pTag 8, .scalar 9 8])).bind
        (decodeTypedValueFromBytesProto 8 (.ref .slice)) =
      some (.aggregate [.ptr pTag 8, .scalar 9 8]) ∧
    (encodeValueToBytesProto 8 (.unaligned .bool) (.aggregate [.scalar (1 : UInt8).toNat 1])).bind
        (decodeTypedValueFromBytesProto 8 (.unaligned .bool)) =
      some (.aggregate [.scalar (1 : UInt8).toNat 1]) :=
  typed_encode_decode_roundtrip 8 (by decide) 0x1234 9 pTag pVt 1 0x41
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl (by decide)

def globalTwoPtrsBytes : List (Option UInt8) :=
  [some 0x40, some 0, some 0, some 0, some 0, some 0, some 0, some 0,
   some 0x40, some 0, some 0, some 0, some 0, some 0, some 0, some 0]

def globalTwoPtrsRelocs : List (Nat × ProvenancePtrProto) :=
  [(0, pTag), (8, pTag)]

theorem t_globalAllocBytesProto_getElem? :
    (encodePtrBytesProto pTag 8).length = 8 ∧
    ∀ (i : Nat), i < 8 →
      ∃ optByte, globalTwoPtrsBytes[0 + i]? = some optByte ∧
        (encodePtrBytesProto pTag 8)[i]? = some (match optByte with
          | none => .uninit
          | some b =>
            match lookupGlobalRelocProto 8 globalTwoPtrsRelocs (0 + i) with
            | some (relocOff, targetPtr) =>
              .init b (some ⟨targetPtr.allocId, targetPtr.tag, (0 + i) - relocOff,
                normOffset 8 targetPtr.offsetBytes, 8⟩)
            | none => .init b none) :=
  globalAllocBytesProto_getElem? 8 globalTwoPtrsBytes globalTwoPtrsRelocs 0 8 _ rfl

/-- Aligned global relocation read recovers `pTag` with exact `tag = 9 ≠ allocId = 5`. -/
theorem t_globalAlloc_aligned_read_exact :
    encodePtrBytesProto pTag 8 = encodePtrBytesProto pTag 8 ∧
    abstractBytesCoherentPtrProvProto 8 (encodePtrBytesProto pTag 8) =
      some ⟨pTag.allocId, pTag.tag, normOffset 8 pTag.offsetBytes⟩ :=
  globalAlloc_aligned_read_exact 8 0 (by decide) globalTwoPtrsBytes globalTwoPtrsRelocs pTag
    (encodePtrBytesProto pTag 8) rfl
    (fun i hi => by
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl)
    (fun i hi => by
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl)

/-- Misaligned global relocation read at offset `1` across `[pTag, pTag]` strips provenance. -/
theorem t_globalAlloc_misaligned_read_strips :
    abstractBytesCoherentPtrProvProto 8
      ((globalAllocBytesProto 8 globalTwoPtrsBytes globalTwoPtrsRelocs 1 8).getD []) = none :=
  globalAlloc_misaligned_read_strips 8 0 1 (by decide) (by decide)
    globalTwoPtrsBytes globalTwoPtrsRelocs pTag 0 _ rfl rfl rfl

/-- 32-bit global relocation at offset `0` does NOT bleed into bytes `4..7`. -/
theorem t_globalAlloc_32bit_no_bleed :
    globalAllocBytesProto 4
      [some 0x10, some 0, some 0, some 0, some 0x42, some 0, some 0, some 0]
      [(0, ⟨1, 9, 0x10⟩)] 4 4 =
      some [mkInitByte 0x42, mkInitByte 0, mkInitByte 0, mkInitByte 0] := rfl

/-- Cross-width image (two 32-bit fragments read as 64-bit): ref UB, raw bare address. -/
theorem t_decode_incoherent_cross_width :
    decodePtrBytesNoForgeProto true .thin 8
        (encodePtrBytesProto pBig4 4 ++ encodePtrBytesProto pBig4 4) = none ∧
    decodeTypedValueFromBytesProto 8 .fnPtr
        (encodePtrBytesProto pBig4 4 ++ encodePtrBytesProto pBig4 4) = none ∧
    decodePtrBytesNoForgeProto false .thin 8
        (encodePtrBytesProto pBig4 4 ++ encodePtrBytesProto pBig4 4) =
      some (.scalar (leValue (leImage 0x11223344 4 ++ leImage 0x11223344 4)) 8) :=
  decode_incoherent_ref_none_raw_scalar 8 (by decide) _ _ rfl rfl
    (coherent_cross_width_none pBig4 pBig4 4 (by decide))

/-- Mixed plain/pointer bytes: ref UB, raw bare address. -/
theorem t_decode_incoherent_mixed_plain :
    decodePtrBytesNoForgeProto true .thin 8 ((encodePtrBytesProto pBig 8).set 3 (mkInitByte 0x55)) =
      none ∧
    decodeTypedValueFromBytesProto 8 .fnPtr ((encodePtrBytesProto pBig 8).set 3 (mkInitByte 0x55)) =
      none ∧
    decodePtrBytesNoForgeProto false .thin 8 ((encodePtrBytesProto pBig 8).set 3 (mkInitByte 0x55)) =
      some (.scalar (leValue ((leImage 0x1122334455667788 8).set 3 0x55)) 8) :=
  decode_incoherent_ref_none_raw_scalar 8 (by decide) _ _ rfl rfl
    (coherent_set_plain_none pBig 8 3 0x55 (by decide))

/-- `UCG#558` value-level: `p = 0` / `p + 256` splice is UB as `&T`, address `256` as `*const T`. -/
theorem t_decode_splice_0_256_value :
    decodePtrBytesNoForgeProto true .thin 8
        (spliceBytes 1 (encodePtrBytesProto pZero 8) (encodePtrBytesProto p256 8)) = none ∧
    decodePtrBytesNoForgeProto false .thin 8
        (spliceBytes 1 (encodePtrBytesProto pZero 8) (encodePtrBytesProto p256 8)) =
      some (.scalar (leValue ((leImage (normOffset 8 0) 8).take 1 ++
        (leImage (normOffset 8 256) 8).drop 1)) 8) :=
  decode_splice_ref_none_raw_scalar pZero p256 8 1 (by decide) (by decide) (by decide)

theorem t_decode_splice_value_address_256 :
    leValue ((leImage (normOffset 8 0) 8).take 1 ++ (leImage (normOffset 8 256) 8).drop 1) = 256 :=
  rfl

/-- Zero-width pointer guard: `ptrBytes = 0` always fails closed (no 0-byte `.scalar 0 0`). -/
theorem t_decode_zero_width_none :
    decodePtrBytesNoForgeProto false .thin 0 [] = none ∧
    decodeScalarLayoutBytesNoForgeProto 0 (.initialized (.pointer 0) ⟨0, 0⟩) [] = none ∧
    decodeScalarLayoutBytesNoForgeProto 0 (.union (.pointer 0)) [] = none ∧
    encodeThinPtrValueProto true 0 (.ptr pZero 0) = none :=
  decode_zero_width_none false true .thin 0 ⟨0, 0⟩ [] (.ptr pZero 0)

/-- Universal `decodeScalarLayoutBytesNoForgeProto` round-trip at 64-bit and 32-bit (with `tag`). -/
theorem t_scalarLayout_encode_ptr_exact :
    (decodeScalarLayoutBytesNoForgeProto 8 (.initialized (.pointer 0) ⟨1, 0xFFFFFFFFFFFFFFFF⟩)
        (encodePtrBytesProto pTag 8) = some (.ptr pTag 8) ∧
     decodeScalarLayoutBytesNoForgeProto 8 (.union (.pointer 0))
        (encodePtrBytesProto pTag 8) = some (.ptr pTag 8)) ∧
    (decodeScalarLayoutBytesNoForgeProto 4 (.initialized (.pointer 0) ⟨1, 0xFFFFFFFF⟩)
        (encodePtrBytesProto pBig4 4) = some (.ptr pBig4 4) ∧
     decodeScalarLayoutBytesNoForgeProto 4 (.union (.pointer 0))
        (encodePtrBytesProto pBig4 4) = some (.ptr pBig4 4)) :=
  ⟨scalarLayout_encode_ptr_exact 8 0 (by decide) ⟨1, 0xFFFFFFFFFFFFFFFF⟩ pTag (by decide),
   scalarLayout_encode_ptr_exact 4 0 (by decide) ⟨1, 0xFFFFFFFF⟩ pBig4 (by decide)⟩

/-- Universal `decodeScalarLayoutBytesNoForgeProto` stripping on reversed all-zero pointer:
`.union` degrades to `.scalar 0 8`; non-null `.initialized` (`start = 1`) rejects `0` as `none`. -/
theorem t_scalarLayout_incoherent_ptr_strips :
    decodeScalarLayoutBytesNoForgeProto 8 (.union (.pointer 0))
        (encodePtrBytesProto pZero 8).reverse = some (.scalar 0 8) ∧
    decodeScalarLayoutBytesNoForgeProto 8 (.initialized (.pointer 0) ⟨1, 0xFFFFFFFFFFFFFFFF⟩)
        (encodePtrBytesProto pZero 8).reverse = none :=
  scalarLayout_incoherent_ptr_strips 8 0 (by decide) ⟨1, 0xFFFFFFFFFFFFFFFF⟩
    (encodePtrBytesProto pZero 8).reverse (leImage 0 8).reverse rfl rfl
    (coherent_reverse_none pZero 8 (by decide))

/-- Universal non-pointer `ScalarLayout`s (`.int`, `.float`) reject pointer fragments. -/
theorem t_scalarLayout_nonPtr_rejects_frag :
    (decodeScalarLayoutBytesNoForgeProto 8 (.initialized (.int 64 false) ⟨0, 0xFFFFFFFFFFFFFFFF⟩)
        (encodePtrBytesProto pBig 8) = none ∧
     decodeScalarLayoutBytesNoForgeProto 8 (.union (.int 64 false))
        (encodePtrBytesProto pBig 8) = none) ∧
    (decodeScalarLayoutBytesNoForgeProto 8 (.initialized (.float 64) ⟨0, 0xFFFFFFFFFFFFFFFF⟩)
        (encodePtrBytesProto pBig 8) = none ∧
     decodeScalarLayoutBytesNoForgeProto 8 (.union (.float 64))
        (encodePtrBytesProto pBig 8) = none) :=
  ⟨scalarLayout_nonPtr_rejects_frag 8 0 _ _ (.int 64 false) ⟨0, 0xFFFFFFFFFFFFFFFF⟩
      (encodePtrBytesProto pBig 8) rfl (fun _ h => by cases h),
   scalarLayout_nonPtr_rejects_frag 8 0 _ _ (.float 64) ⟨0, 0xFFFFFFFFFFFFFFFF⟩
      (encodePtrBytesProto pBig 8) rfl (fun _ h => by cases h)⟩

/-- Universal `ScalarLayout` `bool` (`2u8` UB, `1u8` ok) and `char` surrogate (`0xD800` UB). -/
theorem t_scalarLayout_bool_and_char_validity :
    decodeScalarLayoutBytesNoForgeProto 8 (.initialized (.int 8 false) ⟨0, 1⟩)
        [.init 2 none] = none ∧
    decodeScalarLayoutBytesNoForgeProto 8 (.initialized (.int 8 false) ⟨0, 1⟩)
        [.init 1 none] = some (.scalar 1 1) ∧
    decodeScalarLayoutBytesNoForgeProto 8 (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩)
        (encodeLittleEndianBytesProto 0xD800 4) = none :=
  scalarLayout_bool_and_char_validity 8 2 1 0xD800 (by decide) (by decide) (by decide) (by decide)

/-- Universal Miri wildcard non-rescue on `pZero` / `p256` splice and misplaced concrete fragment. -/
theorem t_miri_wildcard_does_not_rescue_splice :
    inspectFragmentsMirror (some (0, 0))
        [some ⟨0, (0, 0), imageVec8 0⟩,
         some ⟨1, (1, 1), imageVec8 (normOffset 8 0)⟩,
         some ⟨2, (1, 1), imageVec8 (normOffset 8 256)⟩] = .ok none ∧
    inspectFragmentsMirror (some (0, 0))
        [some ⟨0, (0, 0), imageVec8 0⟩,
         some ⟨0, (1, 1), imageVec8 (normOffset 8 0)⟩] = .ok none :=
  miri_wildcard_does_not_rescue_splice (0, 0) pZero p256 (by decide) (by decide) (by decide)

/-- Universal live `MiniRustSpec.Interp.encodePtr` bridge on `pTag` (`allocId = 5, offset = 0x40`). -/
theorem t_mr_encodePtr_eq_proto_8 :
    MiniRustSpec.Interp.encodePtr
        { addr := (0x40 : Int), provenance := some (mrProv 5) } =
      .ok ((encodePtrBytesProto pTag 8).map AbstractByteProto.toMiniRust) :=
  mr_encodePtr_eq_proto_8 pTag (by decide)

/-- Universal live `MiniRustSpec.Interp.encodePtr` → `decodePtr` round-trip on `pTag`. -/
theorem t_mr_encodePtr_decodePtr_roundtrip_8 :
    (MiniRustSpec.Interp.encodePtr
        { addr := (0x40 : Int), provenance := some (mrProv 5) }).bind
        MiniRustSpec.Interp.decodePtr =
      .ok (some { addr := (0x40 : Int), provenance := some (mrProv 5) }) :=
  mr_encodePtr_decodePtr_roundtrip_8 pTag (by decide)

/-- Custom union / partial byte overwrite: even overwriting byte `0` of `pTag` (`offset = 0x40`)
with the IDENTICAL numeric byte `0x40` strips provenance (UB as `&T`/`fnPtr`, `.scalar` as `*const T`). -/
theorem t_partial_byte_overwrite_strips_ptr :
    ∃ buf₁,
      writeBytesProto (encodePtrBytesProto pTag 8) 0 [mkInitByte 0x40] = some buf₁ ∧
      readTypedFromBytesProto 8 (.ref .thin) buf₁ 0 = none ∧
      readTypedFromBytesProto 8 .fnPtr buf₁ 0 = none ∧
      readTypedFromBytesProto 8 (.rawPtr .thin) buf₁ 0 =
        some (.scalar (leValue ((leImage (normOffset 8 0x40) 8).take 0 ++
          [0x40] ++ (leImage (normOffset 8 0x40) 8).drop 1)) 8) :=
  partial_byte_overwrite_strips_ptr pTag 8 0 0x40 (by decide)

/-- Disjoint byte write at offset `8` preserves the pointer `pTag` at offset `0` with exact `tag`. -/
theorem t_disjoint_byte_overwrite_preserves_ptr :
    ∃ buf₁,
      writeBytesProto (encodePtrBytesProto pTag 8 ++ [mkInitByte 0xAA]) 8 [mkInitByte 0x55] =
        some buf₁ ∧
      readTypedFromBytesProto 8 (.ref .thin) buf₁ 0 = some (.ptr pTag 8) :=
  disjoint_byte_overwrite_preserves_ptr true pTag 8 (by decide) (by decide)
    [mkInitByte 0xAA] 0x55 (by decide)

/-! ## 2. Prototype decoders on the adversarial inputs (independent `rfl` checks) -/

/-- Live keeps provenance on these images (`LiveV06.w1_*` / `w2_*`); the prototype on the
corresponding fragment images returns UB for references and a bare address for raw pointers. -/
theorem t_proto_w1_w2_ref_ub :
    decodePtrBytesNoForgeProto true .thin 8 (encodePtrBytesProto ⟨1, 1, 0x1122334455667788⟩ 8).reverse
      = none ∧
    decodePtrBytesNoForgeProto true .thin 4 (encodePtrBytesProto ⟨1, 1, 0x11223344⟩ 4).reverse
      = none ∧
    decodePtrBytesNoForgeProto true .thin 8 (swapFirstTwo (encodePtrBytesProto ⟨1, 1, 0x1122⟩ 8))
      = none ∧
    decodePtrBytesNoForgeProto true .thin 8 (dupFirstByte (encodePtrBytesProto ⟨1, 1, 0x1122⟩ 8))
      = none ∧
    decodePtrBytesNoForgeProto true .thin 8
      (spliceBytes 1 (encodePtrBytesProto ⟨1, 1, 0⟩ 8) (encodePtrBytesProto ⟨1, 1, 4⟩ 8)) = none ∧
    decodePtrBytesNoForgeProto true .thin 8
      (spliceBytes 1 (encodePtrBytesProto ⟨1, 1, 0x10⟩ 8) (encodePtrBytesProto ⟨1, 1, 0x14⟩ 8)) =
      none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem t_proto_w1_raw_address :
    decodePtrBytesNoForgeProto false .thin 8
        (encodePtrBytesProto ⟨1, 1, 0x1122334455667788⟩ 8).reverse =
      some (.scalar 0x8877665544332211 8) ∧
    decodePtrBytesNoForgeProto false .thin 8
        (spliceBytes 1 (encodePtrBytesProto ⟨1, 1, 0⟩ 8) (encodePtrBytesProto ⟨1, 1, 256⟩ 8)) =
      some (.scalar 256 8) := ⟨rfl, rfl⟩

def ptrInit : Trusted.Rustc.V2026_06_01.Layout.ScalarLayout :=
  .initialized (.pointer 0) ⟨1, 0xFFFFFFFFFFFFFFFF⟩

theorem t_proto_scalarLayout :
    decodeScalarLayoutBytesNoForgeProto 8 ptrInit (encodePtrBytesProto pTag 8) =
      some (.ptr pTag 8) ∧
    decodeScalarLayoutBytesNoForgeProto 8 ptrInit
        (encodePtrBytesProto ⟨1, 1, 0x1122334455667788⟩ 8).reverse =
      some (.scalar 0x8877665544332211 8) ∧
    decodeScalarLayoutBytesNoForgeProto 8 ptrInit (encodePtrBytesProto pZero 8).reverse = none ∧
    decodeScalarLayoutBytesNoForgeProto 8 (.union (.pointer 0))
        (spliceBytes 1 (encodePtrBytesProto pZero 8) (encodePtrBytesProto p256 8)) =
      some (.scalar 256 8) ∧
    decodeScalarLayoutBytesNoForgeProto 4 (.union (.pointer 0)) (encodePtrBytesProto pBig4 4) =
      some (.ptr pBig4 4) ∧
    decodeScalarLayoutBytesNoForgeProto 8 (.initialized (.int 8 false) ⟨0, 1⟩)
        [mkInitByte 2] = none ∧
    decodeScalarLayoutBytesNoForgeProto 8 (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩)
        (encodeLittleEndianBytesProto 0xD800 4) = none ∧
    decodeScalarLayoutBytesNoForgeProto 8 (.union (.int 8 false))
        [mkPtrFragByte 0 1 1 0 0 1] = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- W3 on the prototype: reversed vtable half is UB for `&dyn` and a bare address for
`*const dyn`; provenance-carrying slice length and swapped slice halves are rejected; swapped
intact `dyn` halves only move provenance (vtable validity is a separate check). -/
theorem t_proto_w3_wide :
    decodePtrBytesNoForgeProto true .dyn 8
        (encodePtrBytesProto ⟨1, 1, 0x10⟩ 8 ++ (encodePtrBytesProto ⟨2, 2, 0x1122⟩ 8).reverse) =
      none ∧
    decodePtrBytesNoForgeProto false .dyn 8
        (encodePtrBytesProto ⟨1, 1, 0x10⟩ 8 ++ (encodePtrBytesProto ⟨2, 2, 0x1122⟩ 8).reverse) =
      some (.aggregate [.ptr ⟨1, 1, 0x10⟩ 8, .scalar 0x2211000000000000 8]) ∧
    decodePtrBytesNoForgeProto true .slice 8
        (encodePtrBytesProto ⟨1, 1, 0x10⟩ 8 ++ encodePtrBytesProto ⟨2, 2, 3⟩ 8) = none ∧
    decodePtrBytesNoForgeProto false .str 8
        (encodeLittleEndianBytesProto 3 8 ++ encodePtrBytesProto ⟨1, 1, 0x10⟩ 8) = none ∧
    decodePtrBytesNoForgeProto true .dyn 8
        (encodePtrBytesProto ⟨2, 2, 0x40⟩ 8 ++ encodePtrBytesProto ⟨1, 1, 0x10⟩ 8) =
      some (.aggregate [.ptr ⟨2, 2, 0x40⟩ 8, .ptr ⟨1, 1, 0x10⟩ 8]) ∧
    decodePtrBytesNoForgeProto true .dyn 8
        (encodePtrBytesProto ⟨1, 1, 0x10⟩ 8 ++ encodePtrBytesProto ⟨2, 2, 0x20⟩ 4) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Typed encode/decode round trips through the prototype type language. -/
theorem t_proto_typed_roundtrip :
    encodeValueToBytesProto 8 (.ref .dyn) (.aggregate [.ptr pTag 8, .ptr pVt 8]) =
      some (encodePtrBytesProto pTag 8 ++ encodePtrBytesProto pVt 8) ∧
    decodeTypedValueFromBytesProto 8 (.ref .dyn)
        (encodePtrBytesProto pTag 8 ++ encodePtrBytesProto pVt 8) =
      some (.aggregate [.ptr pTag 8, .ptr pVt 8]) ∧
    encodeValueToBytesProto 4 (.rawPtr .slice) (.aggregate [.ptr pBig4 4, .scalar 3 4]) =
      some (encodePtrBytesProto pBig4 4 ++ encodeLittleEndianBytesProto 3 4) ∧
    decodeTypedValueFromBytesProto 4 (.rawPtr .slice)
        (encodePtrBytesProto pBig4 4 ++ encodeLittleEndianBytesProto 3 4) =
      some (.aggregate [.ptr pBig4 4, .scalar 3 4]) ∧
    encodeValueToBytesProto 8 .fnPtr (.ptr pTag 8) = some (encodePtrBytesProto pTag 8) ∧
    decodeTypedValueFromBytesProto 8 .fnPtr (encodePtrBytesProto pTag 8).reverse = none ∧
    decodeTypedValueFromBytesProto 8 (.array .bool 2) [mkInitByte 1, mkInitByte 0] =
      some (.aggregate [.scalar 1 1, .scalar 0 1]) ∧
    decodeTypedValueFromBytesProto 8 (.array .bool 2) [mkInitByte 1, mkInitByte 2] = none ∧
    encodeValueToBytesProto 8 (.array (.uint 1) 2) (.aggregate [.scalar 7 1, .scalar 9 1]) =
      some [mkInitByte 7, mkInitByte 9] ∧
    encodeValueToBytesProto 8 .bool (.scalar 2 1) = none ∧
    encodeValueToBytesProto 8 (.unaligned .bool) (.aggregate [.scalar 1 1]) = some [mkInitByte 1] ∧
    encodeValueToBytesProto 8 (.maybeUninit .bool) (.rawBytes [mkInitByte 2]) =
      some [mkInitByte 2] ∧
    decodeTypedValueFromBytesProto 8 (.uint 1) [mkPtrFragByte 0 1 1 0 0 8] = none ∧
    encodeValueToBytesProto 4 (.rawPtr .slice) (.aggregate [.ptr pBig4 4, .scalar 3 8]) = none ∧
    encodeValueToBytesProto 4 (.rawPtr .slice) (.aggregate [.ptr pBig4 4, .scalar (2 ^ 32) 4]) =
      none ∧
    encodeValueToBytesProto 4 (.rawPtr .thin) (.scalar (2 ^ 32) 4) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## `Kani#5205` scenario chains on the prototype -/

/-- `[u8; 1] = [2]` copied (untyped) into a `MaybeUninit<bool>` buffer: no write-time UB;
`MaybeUninit` read succeeds, `assume_init` (`bool`) read is UB, `u8` read yields `2`;
overwriting with `1` makes the `bool` read yield `true`. -/
theorem t_kani_maybeUninitBool_chain :
    copyNonOverlappingBytesProto [mkInitByte 2] [.uninit] 0 0 1 = some [mkInitByte 2] ∧
    readTypedFromBytesProto 8 (.maybeUninit .bool) [mkInitByte 2] 0 =
      some (.rawBytes [mkInitByte 2]) ∧
    readTypedFromBytesProto 8 .bool [mkInitByte 2] 0 = none ∧
    readTypedFromBytesProto 8 (.uint 1) [mkInitByte 2] 0 = some (.scalar 2 1) ∧
    writeBytesProto [mkInitByte 2] 0 [mkInitByte 1] = some [mkInitByte 1] ∧
    readTypedFromBytesProto 8 .bool [mkInitByte 1] 0 = some (.scalar 1 1) ∧
    readTypedFromBytesProto 8 (.unaligned .bool) [mkInitByte 1] 0 =
      some (.aggregate [.scalar 1 1]) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Copy `2u8` between two `MaybeUninit<bool>` / `[u8; 1]` buffers: no UB. -/
theorem t_kani_copy_between_buffers :
    copyNonOverlappingBytesProto [mkInitByte 2] [mkInitByte 0] 0 0 1 = some [mkInitByte 2] ∧
    copyNonOverlappingBytesProto [mkInitByte 2] [.uninit] 0 0 1 = some [mkInitByte 2] :=
  ⟨rfl, rfl⟩

/-- `Unaligned<bool>` at unaligned offset `1` of a `[u8; 4]` buffer. -/
theorem t_kani_unaligned_offset1 :
    readTypedFromBytesProto 8 (.unaligned .bool)
        [mkInitByte 7, mkInitByte 1, mkInitByte 9, mkInitByte 9] 1 =
      some (.aggregate [.scalar 1 1]) ∧
    readTypedFromBytesProto 8 (.unaligned .bool)
        [mkInitByte 7, mkInitByte 0, mkInitByte 9, mkInitByte 9] 1 =
      some (.aggregate [.scalar 0 1]) ∧
    readTypedFromBytesProto 8 (.unaligned .bool)
        [mkInitByte 7, mkInitByte 2, mkInitByte 9, mkInitByte 9] 1 = none :=
  ⟨rfl, rfl, rfl⟩

/-- Nested `MaybeUninit<Unaligned<bool>>` holding `2u8`. -/
theorem t_kani_nested_union :
    readTypedFromBytesProto 8 (.maybeUninit (.unaligned .bool)) [mkInitByte 2] 0 =
      some (.rawBytes [mkInitByte 2]) ∧
    readTypedFromBytesProto 8 (.unaligned .bool) [mkInitByte 2] 0 = none :=
  ⟨rfl, rfl⟩

/-- `write_bytes(dst, 2, 1)` into `bool` / `MaybeUninit<bool>` storage: no write-time UB. -/
theorem t_kani_write_bytes :
    writeBytesFillProto [.uninit] 0 2 1 = some [mkInitByte 2] ∧
    readTypedFromBytesProto 8 .bool [mkInitByte 2] 0 = none ∧
    writeBytesFillProto [mkInitByte 0, mkInitByte 0] 0 0xFF 2 =
      some [mkInitByte 0xFF, mkInitByte 0xFF] :=
  ⟨rfl, rfl, rfl⟩

/-- `char` surrogate `0xD800` written untyped, then read typed. -/
theorem t_kani_char_surrogate :
    writeBytesProto (List.replicate 4 .uninit) 0 (encodeLittleEndianBytesProto 0xD800 4) =
      some (encodeLittleEndianBytesProto 0xD800 4) ∧
    readTypedFromBytesProto 8 .char (encodeLittleEndianBytesProto 0xD800 4) 0 = none ∧
    readTypedFromBytesProto 8 (.uint 4) (encodeLittleEndianBytesProto 0xD800 4) 0 =
      some (.scalar 0xD800 4) ∧
    readTypedFromBytesProto 8 .char (encodeLittleEndianBytesProto 0x41 4) 0 =
      some (.scalar 0x41 4) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Out-of-bounds copies and reads fail; in-bounds ones never depend on byte values. -/
theorem t_kani_bounds :
    copyNonOverlappingBytesProto [mkInitByte 2] [.uninit] 0 1 1 = none ∧
    readTypedFromBytesProto 8 .bool [mkInitByte 1] 1 = none :=
  ⟨rfl, rfl⟩

/-! ## 3. Restatements of every concrete live / MiniRust / Miri witness -/

namespace RestateLiveV06

open Anneal.Proto.Ucg558PtrByteCoherenceProto
open Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06
open Trusted Trusted.Rustc.V2026_06_01.MirSemantics Trusted.Rustc.V2026_06_01.MirAst
  Trusted.Rustc.V2026_06_01.Layout

theorem t_w1_rev8_raw :
    decodePtrBytesNoForge false thinTy 8 (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_rev8_raw

theorem t_w1_rev8_ref :
    decodePtrBytesNoForge true thinTy 8 (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_rev8_ref

theorem t_w1_rev8_zero_ref :
    decodePtrBytesNoForge true thinTy 8 (liveEnc 1 1 0 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_rev8_zero_ref

theorem t_w1_rev4_raw :
    decodePtrBytesNoForge false thinTy 4 (liveEnc 1 1 0x11223344 4).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x44332211 } 4) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_rev4_raw

theorem t_w1_rev4_ref :
    decodePtrBytesNoForge true thinTy 4 (liveEnc 1 1 0x11223344 4).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x44332211 } 4) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_rev4_ref

theorem t_w1_swap01_ref :
    decodePtrBytesNoForge true thinTy 8 (swapFirstTwo (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_swap01_ref

theorem t_w1_swap01_raw :
    decodePtrBytesNoForge false thinTy 8 (swapFirstTwo (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_swap01_raw

theorem t_w1_dup0_ref :
    decodePtrBytesNoForge true thinTy 8 (dupFirstByte (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2222222222222222 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_dup0_ref

theorem t_w1_dup0_raw :
    decodePtrBytesNoForge false thinTy 8 (dupFirstByte (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2222222222222222 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_dup0_raw

theorem t_w1_scalarInit_rev8 :
    decodeScalarLayoutBytesNoForge ptrScalarInit (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_scalarInit_rev8

theorem t_w1_scalarUnion_rev8 :
    decodeScalarLayoutBytesNoForge ptrScalarUnion (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_scalarUnion_rev8

theorem t_w1_scalarInit_swap01 :
    decodeScalarLayoutBytesNoForge ptrScalarInit (swapFirstTwo (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_scalarInit_swap01

theorem t_w1_scalarUnion_dup0 :
    decodeScalarLayoutBytesNoForge ptrScalarUnion (dupFirstByte (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2222222222222222 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_scalarUnion_dup0

theorem t_w1_typed_rawPtr_rev8_64bit :
    decodeTypedValueFromBytes 16 layouts64 rawPtrTy (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_typed_rawPtr_rev8_64bit

theorem t_w1_typed_rawPtr_rev4_32bit :
    decodeTypedValueFromBytes 16 layouts32 rawPtrTy (liveEnc 1 1 0x11223344 4).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x44332211 } 4) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_typed_rawPtr_rev4_32bit

theorem t_w2_splice_0_4_ref :
    decodePtrBytesNoForge true thinTy 8 (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 4 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w2_splice_0_4_ref

theorem t_w2_splice_10_14_ref :
    decodePtrBytesNoForge true thinTy 8
      (spliceBytes 1 (liveEnc 1 1 0x10 8) (liveEnc 1 1 0x14 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x10 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w2_splice_10_14_ref

theorem t_w2_splice_0_256_ref :
    decodePtrBytesNoForge true thinTy 8 (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 256 8)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w2_splice_0_256_ref

theorem t_w2_splice_0_256_raw :
    decodePtrBytesNoForge false thinTy 8 (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 256 8)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w2_splice_0_256_raw

theorem t_w2_splice_0_256_rev4_ref :
    decodePtrBytesNoForge true thinTy 4 (spliceBytes 1 (liveEnc 1 1 0 4) (liveEnc 1 1 256 4)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 4) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w2_splice_0_256_rev4_ref

theorem t_w2_scalarInit_splice_0_256 :
    decodeScalarLayoutBytesNoForge ptrScalarInit
      (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 256 8)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w2_scalarInit_splice_0_256

theorem t_w2_scalarUnion_splice_10_14 :
    decodeScalarLayoutBytesNoForge ptrScalarUnion
      (spliceBytes 1 (liveEnc 1 1 0x10 8) (liveEnc 1 1 0x14 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x10 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w2_scalarUnion_splice_10_14

theorem t_w3_dyn_rev_vtable_ref :
    decodePtrBytesNoForge true (.dynamic "Trait") 8
      (liveEnc 1 1 0x10 8 ++ (liveEnc 2 2 0x1122 8).reverse) =
      some (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8,
        .ptr { allocId := 2, offsetBytes := 0x2211000000000000 } 8]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w3_dyn_rev_vtable_ref

theorem t_w3_dyn_rev_vtable_raw :
    decodePtrBytesNoForge false (.dynamic "Trait") 8
      (liveEnc 1 1 0x10 8 ++ (liveEnc 2 2 0x1122 8).reverse) =
      some (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8,
        .ptr { allocId := 2, offsetBytes := 0x2211000000000000 } 8]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w3_dyn_rev_vtable_raw

theorem t_w3_dyn_swapped_halves_ref :
    decodePtrBytesNoForge true (.dynamic "Trait") 8 (liveEnc 2 2 0x40 8 ++ liveEnc 1 1 0x10 8) =
      some (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0x40 } 8,
        .ptr { allocId := 1, offsetBytes := 0x10 } 8]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w3_dyn_swapped_halves_ref

theorem t_w3_slice_prov_len_ref :
    decodePtrBytesNoForge true (.slice thinTy) 8 (liveEnc 1 1 0x10 8 ++ liveEnc 2 2 3 8) = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w3_slice_prov_len_ref

theorem t_w3_slice_swapped_raw :
    decodePtrBytesNoForge false (.slice thinTy) 8 (livePlain 3 8 ++ liveEnc 1 1 0x10 8) = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w3_slice_swapped_raw

theorem t_w3_str_intact_ref :
    decodePtrBytesNoForge true .str 8 (liveEnc 1 1 0x10 8 ++ livePlain 3 8) =
      some (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8, .scalar ⟨3, 8⟩]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w3_str_intact_ref

theorem t_w3_tag_dropped_on_decode :
    decodePtrBytesNoForge true thinTy 8 (liveEnc 5 9 0x40 8) =
      some (.ptr { allocId := 5, offsetBytes := 0x40 } 8) ∧
    ProvenancePtr.tag { allocId := 5, offsetBytes := 0x40 } = 5 :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w3_tag_dropped_on_decode

theorem t_w3_live_encode_writes_allocId_as_tag :
    encodeValueToBytes 16 layouts64 rawPtrTy (.ptr { allocId := 7, offsetBytes := 0x40 } 8) =
      some (liveEnc 7 7 0x40 8) ∧
    decodePtrBytesNoForge false thinTy 8 (liveEnc 7 7 0x40 8) =
      some (.ptr { allocId := 7, offsetBytes := 0x40 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w3_live_encode_writes_allocId_as_tag

theorem t_w3_mixed_tag_stripped_ref :
    decodePtrBytesNoForge true thinTy 8 (spliceBytes 4 (liveEnc 5 9 0x40 8) (liveEnc 5 10 0x40 8)) =
      none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w3_mixed_tag_stripped_ref

theorem t_w3_dyn_plain_vtable_ref_unsound :
    decodePtrBytesNoForge true (.dynamic "Trait") 8
      (liveEnc 1 1 0x10 8 ++ livePlain 0x1122 8) =
      some (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8, .scalar ⟨0x1122, 8⟩]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w3_dyn_plain_vtable_ref_unsound

theorem t_w3_dyn_encode_vtable_ptr_none :
    encodeValueToBytes 16 layouts64 dynRefTy
      (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8,
        .ptr { allocId := 2, offsetBytes := 0x1000 } 8]) = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w3_dyn_encode_vtable_ptr_none

theorem t_w3_raw_overlay_drops_tag_and_frag :
    overlayRawAbstractByteVals (encodeRawAbstractByteVals (liveEnc 5 9 0x40 8))
      (replicateUninitBytes 8) = some (liveEnc 5 5 0x40 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w3_raw_overlay_drops_tag_and_frag

theorem t_w1_decodeValueFromBytes_forges_prov :
    decodeValueFromBytes 16 layouts64 rawPtrTy (livePlain 0x20004 8) =
      some (.ptr { allocId := 2, offsetBytes := 4 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_decodeValueFromBytes_forges_prov

theorem t_w1_scalarLayout_32bit_none :
    decodeScalarLayoutBytesNoForge ptrScalarInit (liveEnc 1 1 0x11223344 4) = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_scalarLayout_32bit_none

theorem t_w4_global_misaligned_cross_reloc_unsound :
    (match globalAllocSliceToAbstractBytes globalTwoPtrsAlloc 1 8 with
      | some bs => decodePtrBytesNoForge true thinTy 8 bs
      | none => none) =
      some (.ptr { allocId := 1, offsetBytes := 0x1000000000000000 } 8) ∧
    (match globalAllocSliceToAbstractBytes globalTwoPtrsAlloc 4 8 with
      | some bs => decodePtrBytesNoForge false thinTy 8 bs
      | none => none) =
      some (.ptr { allocId := 1, offsetBytes := 0x0000001000000000 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w4_global_misaligned_cross_reloc_unsound

theorem t_w4_global_32bit_reloc_bleeds :
    globalAllocSliceToAbstractBytes
      { allocId := 100,
        bytes := [some 0x10, some 0, some 0, some 0, some 0x42, some 0, some 0, some 0],
        relocations := [(0, { allocId := 1, offsetBytes := 0x10 })],
        align := ⟨4⟩,
        mutability := .not } 4 4 =
      some [.init 0x42 (some (1, 1)), .init 0 (some (1, 1)),
            .init 0 (some (1, 1)), .init 0 (some (1, 1))] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w4_global_32bit_reloc_bleeds

theorem t_k_decode_bool_2_none :
    decodeTypedValueFromBytes 16 kLayouts tyBool [.init 2 none] = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_decode_bool_2_none

theorem t_k_decode_u8_2 :
    decodeTypedValueFromBytes 16 kLayouts tyU8 [.init 2 none] = some (.scalar ⟨2, 1⟩) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_decode_u8_2

theorem t_k_decode_maybeUninitBool_2 :
    decodeTypedValueFromBytes 16 kLayouts tyMUBool [.init 2 none] =
      some (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_decode_maybeUninitBool_2

theorem t_k_decode_nested_maybeUninitBool_2 :
    decodeTypedValueFromBytes 16 kLayouts tyMUMUBool [.init 2 none] =
      some (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_decode_nested_maybeUninitBool_2

theorem t_k_decode_unalignedBool_2_none :
    decodeTypedValueFromBytes 16 kLayouts tyUnalBool [.init 2 none] = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_decode_unalignedBool_2_none

theorem t_k_decode_unalignedBool_1 :
    decodeTypedValueFromBytes 16 kLayouts tyUnalBool [.init 1 none] =
      some (.aggregate 0 [.scalar ⟨1, 1⟩]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_decode_unalignedBool_1

theorem t_k_decode_unalignedBool_offset1 :
    (match sliceAbstractBytes [.init 7 none, .init 1 none, .init 9 none, .init 9 none] 1 1 with
      | some bs => decodeTypedValueFromBytes 16 kLayouts tyUnalBool bs
      | none => none) = some (.aggregate 0 [.scalar ⟨1, 1⟩]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_decode_unalignedBool_offset1

theorem t_k_decode_maybeUninitUnaligned_2 :
    decodeTypedValueFromBytes 16 kLayouts tyMUUnal [.init 2 none] =
      some (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_decode_maybeUninitUnaligned_2

theorem t_k_decode_char_surrogate :
    decodeTypedValueFromBytes 16 kLayouts tyChar (livePlain 0xD800 4) = none ∧
    decodeTypedValueFromBytes 16 kLayouts tyU32 (livePlain 0xD800 4) = some (.scalar ⟨0xD800, 4⟩) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_decode_char_surrogate

theorem t_k_copy_u8arr_to_maybeUninitBool :
    stepOutcome (copyActive tyU8A1 tyMUBool u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.unit, .scalar ⟨2, 1⟩]))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_copy_u8arr_to_maybeUninitBool

theorem t_k_copy_u8arr_to_nestedMaybeUninitBool :
    stepOutcome (copyActive tyU8A1 tyMUMUBool u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.unit, .scalar ⟨2, 1⟩]))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_copy_u8arr_to_nestedMaybeUninitBool

theorem t_k_copy_u8arr_to_u8arr :
    stepOutcome (copyActive tyU8A1 tyU8A1 u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.scalar ⟨2, 1⟩]))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_copy_u8arr_to_u8arr

theorem t_k_copy_maybeUninit_to_maybeUninit :
    stepOutcome (copyActive tyMUBool tyMUBool muBool2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.unit, .scalar ⟨2, 1⟩])) muBool2) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_copy_maybeUninit_to_maybeUninit

theorem t_k_copy_union_to_nonunion :
    stepOutcome (copyActive tyMUBool tyU8A1 muBool2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.scalar ⟨2, 1⟩])) muBool2) [] ∧
    stepOutcome (copyActive tyMUBool tyBool muBool2 .uninit) = .ub ∧
    stepOutcome (copyActive tyMUBool tyUnalBool muBool2 .uninit) = .ub :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_copy_union_to_nonunion

theorem t_k_copy_u8arr_to_bool_premature_ub :
    stepOutcome (copyActive tyU8A1 tyBool u8Arr2 .uninit) = .ub :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_copy_u8arr_to_bool_premature_ub

theorem t_k_copy_u8_to_bool_premature_ub :
    stepOutcome (copyActive tyU8 tyBool u8Scalar2 .uninit) = .ub :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_copy_u8_to_bool_premature_ub

theorem t_k_copy_u8arr_to_unalignedBool :
    stepOutcome (copyActive tyU8A1 tyUnalBool u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.scalar ⟨2, 1⟩]))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_copy_u8arr_to_unalignedBool

theorem t_k_copy_u8_to_unalignedBool_shape_vs_typed :
    stepOutcome (copyActive tyU8 tyUnalBool u8Scalar2 .uninit) =
      .step (activeLocals (.init (.scalar ⟨2, 1⟩)) u8Scalar2) [] ∧
    stepOutcome (copyActiveEx tyU8 tyUnalBool tyPtrU8 tyPtrUnalBool 0 0 1 u8Scalar2 .uninit) = .ub :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_copy_u8_to_unalignedBool_shape_vs_typed

theorem t_k_copy_u8arr_to_maybeUninitUnaligned :
    stepOutcome (copyActive tyU8A1 tyMUUnal u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.unit, .scalar ⟨2, 1⟩]))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_copy_u8arr_to_maybeUninitUnaligned

theorem t_k_copy_subplace_multi_audit :
    stepOutcome (copyActiveEx tyU8A2 tyBoolA2 tyPtrU8 tyPtrU8 0 0 2 u8Arr12 .uninit) = .unsupported ∧
    stepOutcome (copyActiveEx tyU8A4 tyBool tyPtrU8 tyPtrU8 1 0 1 u8Arr4Bad .uninit) = .unsupported ∧
    stepOutcome (copyActiveEx tyU8A4 tyUnalBool tyPtrU8 tyPtrU8 1 0 1 u8Arr4Bad .uninit) =
      .unsupported ∧
    stepOutcome (copyActiveEx tyU8A4 tyUnalBool tyPtrU8 tyPtrU8 1 0 1 u8Arr4Ok .uninit) =
      .unsupported ∧
    stepOutcome (copyActiveEx tyU8A4 tyBool tyPtrU8 tyPtrU8 1 0 1 u8Arr4Ok .uninit) =
      .step (activeLocalsAt 1 0 (.init (.scalar ⟨1, 1⟩)) u8Arr4Ok) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_copy_subplace_multi_audit

theorem t_k_gap_unalignedBool_field_reads_2 :
    copyThenRead tyU8A1 tyUnalBool u8Arr2 [.field 0 tyBool] = .ok (.scalar ⟨2, 1⟩) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_gap_unalignedBool_field_reads_2

theorem t_k_gap_unalignedBool_whole_reads_2 :
    copyThenRead tyU8A1 tyUnalBool u8Arr2 [] = .ok (.aggregate 0 [.scalar ⟨2, 1⟩]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_gap_unalignedBool_whole_reads_2

theorem t_k_gap_maybeUninitUnaligned_assume_init :
    copyThenRead tyU8A1 tyMUUnal u8Arr2 [.field 1 tyUnalBool] =
      .ok (.scalar ⟨2, 1⟩) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_gap_maybeUninitUnaligned_assume_init

theorem t_k_maybeUninitBool_assume_init_ub :
    copyThenRead tyU8A1 tyMUBool u8Arr2 [.field 1 tyBool] = .ub :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_maybeUninitBool_assume_init_ub

theorem t_k_maybeUninitUnaligned_inner_field_ub :
    copyThenRead tyU8A1 tyMUUnal u8Arr2 [.field 1 tyUnalBool, .field 0 tyBool] = .ub :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_maybeUninitUnaligned_inner_field_ub

theorem t_k_bool_local_holding_2_reads_ok :
    readOutcome (evalOperand [.init .unit, .uninit, .init (.scalar ⟨2, 1⟩)] (.copy (lc 2)) [] []
      kLayouts [] [decl tyUnit, decl tyU8A1, decl tyBool] []) = .ok (.scalar ⟨2, 1⟩) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_bool_local_holding_2_reads_ok

theorem t_k_gap_foreign_u8_to_bool_stores_2 :
    stepOutcome (copyForeign tyU8 tyBool u8Scalar2 .uninit) =
      .step (foreignActive u8Scalar2) [[.init .unit, .init (.scalar ⟨2, 1⟩)]] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_gap_foreign_u8_to_bool_stores_2

theorem t_k_gap_foreign_u8arr_to_bool_stores_array :
    stepOutcome (copyForeign tyU8A1 tyBool u8Arr2 .uninit) =
      .step (foreignActive u8Arr2) [[.init .unit, .init (.aggregate 0 [.scalar ⟨2, 1⟩])]] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_gap_foreign_u8arr_to_bool_stores_array

theorem t_k_foreign_u8_to_maybeUninitBool :
    stepOutcome (copyForeign tyU8 tyMUBool u8Scalar2 .uninit) =
      .step (foreignActive u8Scalar2) [[.init .unit, .init (.scalar ⟨2, 1⟩)]] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_foreign_u8_to_maybeUninitBool

theorem t_k_writeBytes_bool_2_unsupported :
    writeBytesOutcome tyBool .bool 2 = .unsupported :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_writeBytes_bool_2_unsupported

theorem t_k_writeBytes_bool_1_store :
    writeBytesOutcome tyBool .bool 1 = .store (.scalar ⟨1, 1⟩) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_writeBytes_bool_1_store

theorem t_k_writeBytes_maybeUninitBool_unsupported :
    writeBytesOutcome tyMUBool tyMUBool.kind 2 = .unsupported :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_writeBytes_maybeUninitBool_unsupported

theorem t_k_writeBytes_u8arr_unsupported :
    writeBytesOutcome tyU8A1 (.uint .u8) 2 = .unsupported :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_writeBytes_u8arr_unsupported

theorem t_k_writeBytes_u8_store :
    writeBytesOutcome tyU8 (.uint .u8) 2 = .store (.scalar ⟨2, 1⟩) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_writeBytes_u8_store

theorem t_k_writeBytes_unalignedBool_unsupported :
    writeBytesOutcome tyUnalBool tyUnalBool.kind 2 = .unsupported :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_writeBytes_unalignedBool_unsupported

theorem t_k_writeBytes_char_ff_unsupported :
    writeBytesOutcome tyChar .char 0xFF = .unsupported :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_writeBytes_char_ff_unsupported

theorem t_proto_projects_to_liveEnc :
    (encodePtrBytesProto ⟨1, 1, 0x1122334455667788⟩ 8).map AbstractByteProto.toLive06 =
      liveEnc 1 1 0x1122334455667788 8 :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.proto_projects_to_liveEnc

theorem t_k_gap_union_to_ptr_forges_provenance :
    stepOutcome (copyActiveEx tyMUPtr tyRawU8 tyPtrRawU8 tyPtrRawU8 0 0 1 muPtrPlain .uninit) =
      .step (activeLocals (.init (.ptr { allocId := 2, offsetBytes := 4 } 8)) muPtrPlain) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_gap_union_to_ptr_forges_provenance

theorem t_k_copy_usize_to_ptr_no_forge :
    stepOutcome (copyActiveEx tyUsize tyRawU8 tyPtrRawU8 tyPtrRawU8 0 0 1
      (.init (.scalar ⟨0x20004, 8⟩)) .uninit) =
      .step (activeLocals (.init (.scalar ⟨0x20004, 8⟩)) (.init (.scalar ⟨0x20004, 8⟩))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_copy_usize_to_ptr_no_forge

theorem t_k_gap_singleDirect_usize_to_ptr_forges_provenance :
    stepOutcome (copyActiveEx tyUsize tyRawU8 tyPtrUsize tyPtrRawU8 0 0 1
      (.init (.scalar ⟨0x20004, 8⟩)) .uninit) =
      .step (activeLocals (.init (.ptr { allocId := 2, offsetBytes := 4 } 8))
        (.init (.scalar ⟨0x20004, 8⟩))) [] ∧
    stepOutcome (copyActiveEx tyUsize tyRefU8 tyPtrUsize tyPtrRefU8 0 0 1
      (.init (.scalar ⟨0x20004, 8⟩)) .uninit) =
      .step (activeLocals (.init (.ptr { allocId := 2, offsetBytes := 4 } 8))
        (.init (.scalar ⟨0x20004, 8⟩))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_gap_singleDirect_usize_to_ptr_forges_provenance

theorem t_k_copy_subplaceMulti_u8arr8_to_ptr_unsupported :
    stepOutcome (copyActiveEx tyU8A8 tyRawU8 tyPtrU8 tyPtrU8 0 0 8 u8Arr8Addr .uninit) =
      .unsupported ∧
    stepOutcome (copyActiveEx tyU8A8 tyRefU8 tyPtrU8 tyPtrU8 0 0 8 u8Arr8Addr .uninit) =
      .unsupported :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_copy_subplaceMulti_u8arr8_to_ptr_unsupported

theorem t_k_gap_ptr_to_usize_keeps_provenance :
    stepOutcome (copyActiveEx tyRawU8 tyUsize tyPtrRawU8 tyPtrRawU8 0 0 1
      (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8)) .uninit) =
      .step (activeLocals (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8))
        (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8))) [] ∧
    readOutcome (evalOperand [.init .unit, .uninit,
        .init (.ptr { allocId := 7, offsetBytes := 0x40 } 8)] (.copy (lc 2)) [] [] kLayouts []
      [decl tyUnit, decl tyUnit, decl tyUsize] []) =
      .ok (.ptr { allocId := 7, offsetBytes := 0x40 } 8) ∧
    stepOutcome (copyActiveEx tyRawU8 tyUsize tyPtrRawU8 tyPtrUsize 0 0 1
      (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8)) .uninit) =
      .step (activeLocals (.init (.scalar ⟨0x40, 8⟩))
        (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_gap_ptr_to_usize_keeps_provenance

theorem t_k_copy_ptr_bytewise_unsupported :
    stepOutcome (copyActiveEx tyRawU8 tyU8A8 tyPtrU8 tyPtrU8 0 0 8
      (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8)) u8Arr8Zero) = .unsupported ∧
    stepOutcome (copyActiveEx tyRawU8 tyU8A4 tyPtrU8 tyPtrU8 0 0 4
      (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8)) .uninit) = .unsupported ∧
    stepOutcome (copyActiveEx tyRawU8 tyRawU8 tyPtrU8 tyPtrU8 0 0 8
      (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8)) .uninit) = .unsupported :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_copy_ptr_bytewise_unsupported

theorem t_k_gap_foreign_usize_to_ptr_forges_provenance :
    stepOutcome (copyForeignEx tyUsize tyRawU8 tyPtrUsize tyPtrRawU8
      (.init (.scalar ⟨0x20004, 8⟩)) .uninit) =
      .step (foreignActive (.init (.scalar ⟨0x20004, 8⟩)))
        [[.init .unit, .init (.ptr { allocId := 2, offsetBytes := 4 } 8)]] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.k_gap_foreign_usize_to_ptr_forges_provenance

theorem t_w1_encode_32bit_ptr_none :
    encodeValueToBytes 16 layouts32 rawPtrTy (.ptr { allocId := 1, offsetBytes := 0x10 } 4) =
      none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w1_encode_32bit_ptr_none

theorem t_w3_wide_swapped_halves_matrix :
    decodePtrBytesNoForge false .str 8 (livePlain 3 8 ++ liveEnc 1 1 0x10 8) = none ∧
    decodePtrBytesNoForge true .str 8 (livePlain 3 8 ++ liveEnc 1 1 0x10 8) = none ∧
    decodePtrBytesNoForge true (.slice thinTy) 8 (livePlain 3 8 ++ liveEnc 1 1 0x10 8) = none ∧
    decodePtrBytesNoForge true .str 8 (liveEnc 1 1 0x10 8 ++ liveEnc 2 2 3 8) = none ∧
    decodePtrBytesNoForge false (.dynamic "Trait") 8 (liveEnc 2 2 0x40 8 ++ liveEnc 1 1 0x10 8) =
      some (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0x40 } 8,
        .ptr { allocId := 1, offsetBytes := 0x10 } 8]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w3_wide_swapped_halves_matrix

theorem t_w4_const_indirect_forges_prov :
    evalConstValue (.indirect 101 0) rawPtrTy [globalPlainAddrAlloc] layouts64 =
      some (.ptr { allocId := 2, offsetBytes := 4 } 8) ∧
    evalConstValue (.indirect 101 0) tyRefU8 [globalPlainAddrAlloc] layouts64 =
      some (.ptr { allocId := 2, offsetBytes := 4 } 8) ∧
    evalConstValue (.slice (.int ⟨0x20004, 8⟩) 5)
        { kind := .rawPtr .not (.slice thinTy), layoutIdx := 0 } [] layouts64 =
      some (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 4 } 8, .scalar ⟨5, 8⟩]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w4_const_indirect_forges_prov

theorem t_w4_decodeValueFromBytes_single_mixed_byte_unsound :
    decodeValueFromBytes 16 layouts64 rawPtrTy
        ([.init 0x10 (some (1, 1))] ++ livePlain 0 7) =
      some (.ptr { allocId := 1, offsetBytes := 0x10 } 8) ∧
    decodeValueFromBytes 16 layouts64 tyRefU8
        ([.init 0x10 (some (1, 1))] ++ livePlain 0 7) =
      some (.ptr { allocId := 1, offsetBytes := 0x10 } 8) ∧
    decodeValueFromBytes 16 layouts64 tyRefU8
        (spliceBytes 1 (liveEnc 1 1 0x10 8) (liveEnc 2 2 0x200 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x210 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w4_decodeValueFromBytes_single_mixed_byte_unsound

theorem t_w5_byteCast_transmute_audit :
    byteCastOutcome tyMUPtr tyRefU8 muPtrRevVal =
      .ok (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) ∧
    byteCastOutcome tyMUPtr tyRefU8 muPtrSpliceVal =
      .ok (.ptr { allocId := 1, offsetBytes := 256 } 8) ∧
    byteCastOutcome tyUsize tyRawU8 (.scalar ⟨0x20004, 8⟩) = .ok (.scalar ⟨0x20004, 8⟩) ∧
    byteCastOutcome tyUsize tyRefU8 (.scalar ⟨0x20004, 8⟩) = .ub ∧
    byteCastOutcome tyRawU8 tyUsize (.ptr { allocId := 7, offsetBytes := 0x40 } 8) = .ub ∧
    byteCastOutcome tyU8 tyBool (.scalar ⟨2, 1⟩) = .ub ∧
    byteCastOutcome tyU8 tyUnalBool (.scalar ⟨2, 1⟩) = .ub ∧
    byteCastOutcome tyU8 tyMUBool (.scalar ⟨2, 1⟩) =
      .ok (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w5_byteCast_transmute_audit

theorem t_w5_enum_multiple_allows_prov_bytes :
    decodeTypedValueFromBytes 16 enumTagLayouts tyEnumTag2 [.init 1 (some (1, 1))] =
      some (.aggregate 1 []) ∧
    decodeTypedValueFromBytes 16 kLayouts tyBool [.init 1 (some (1, 1))] = none ∧
    decodeTypedValueFromBytes 16 kLayouts tyU8 [.init 1 (some (1, 1))] = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV06.w5_enum_multiple_allows_prov_bytes

end RestateLiveV06

namespace RestateLiveV08

open Anneal.Proto.Ucg558PtrByteCoherenceProto
open Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08
open Trusted Trusted.Rustc.V2026_08_01.MirSemantics Trusted.Rustc.V2026_08_01.MirAst
  Trusted.Rustc.V2026_08_01.Layout

theorem t_w1_rev8_raw :
    decodePtrBytesNoForge false thinTy 8 (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_rev8_raw

theorem t_w1_rev8_ref :
    decodePtrBytesNoForge true thinTy 8 (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_rev8_ref

theorem t_w1_rev8_zero_ref :
    decodePtrBytesNoForge true thinTy 8 (liveEnc 1 1 0 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_rev8_zero_ref

theorem t_w1_rev4_raw :
    decodePtrBytesNoForge false thinTy 4 (liveEnc 1 1 0x11223344 4).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x44332211 } 4) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_rev4_raw

theorem t_w1_rev4_ref :
    decodePtrBytesNoForge true thinTy 4 (liveEnc 1 1 0x11223344 4).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x44332211 } 4) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_rev4_ref

theorem t_w1_swap01_ref :
    decodePtrBytesNoForge true thinTy 8 (swapFirstTwo (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_swap01_ref

theorem t_w1_swap01_raw :
    decodePtrBytesNoForge false thinTy 8 (swapFirstTwo (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_swap01_raw

theorem t_w1_dup0_ref :
    decodePtrBytesNoForge true thinTy 8 (dupFirstByte (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2222222222222222 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_dup0_ref

theorem t_w1_dup0_raw :
    decodePtrBytesNoForge false thinTy 8 (dupFirstByte (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2222222222222222 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_dup0_raw

theorem t_w1_scalarInit_rev8 :
    decodeScalarLayoutBytesNoForge ptrScalarInit (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_scalarInit_rev8

theorem t_w1_scalarUnion_rev8 :
    decodeScalarLayoutBytesNoForge ptrScalarUnion (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_scalarUnion_rev8

theorem t_w1_scalarInit_swap01 :
    decodeScalarLayoutBytesNoForge ptrScalarInit (swapFirstTwo (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_scalarInit_swap01

theorem t_w1_scalarUnion_dup0 :
    decodeScalarLayoutBytesNoForge ptrScalarUnion (dupFirstByte (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2222222222222222 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_scalarUnion_dup0

theorem t_w1_typed_rawPtr_rev8_64bit :
    decodeTypedValueFromBytes 16 layouts64 rawPtrTy (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_typed_rawPtr_rev8_64bit

theorem t_w1_typed_rawPtr_rev4_32bit :
    decodeTypedValueFromBytes 16 layouts32 rawPtrTy (liveEnc 1 1 0x11223344 4).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x44332211 } 4) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_typed_rawPtr_rev4_32bit

theorem t_w2_splice_0_4_ref :
    decodePtrBytesNoForge true thinTy 8 (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 4 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w2_splice_0_4_ref

theorem t_w2_splice_10_14_ref :
    decodePtrBytesNoForge true thinTy 8
      (spliceBytes 1 (liveEnc 1 1 0x10 8) (liveEnc 1 1 0x14 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x10 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w2_splice_10_14_ref

theorem t_w2_splice_0_256_ref :
    decodePtrBytesNoForge true thinTy 8 (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 256 8)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w2_splice_0_256_ref

theorem t_w2_splice_0_256_raw :
    decodePtrBytesNoForge false thinTy 8 (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 256 8)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w2_splice_0_256_raw

theorem t_w2_splice_0_256_rev4_ref :
    decodePtrBytesNoForge true thinTy 4 (spliceBytes 1 (liveEnc 1 1 0 4) (liveEnc 1 1 256 4)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 4) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w2_splice_0_256_rev4_ref

theorem t_w2_scalarInit_splice_0_256 :
    decodeScalarLayoutBytesNoForge ptrScalarInit
      (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 256 8)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w2_scalarInit_splice_0_256

theorem t_w2_scalarUnion_splice_10_14 :
    decodeScalarLayoutBytesNoForge ptrScalarUnion
      (spliceBytes 1 (liveEnc 1 1 0x10 8) (liveEnc 1 1 0x14 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x10 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w2_scalarUnion_splice_10_14

theorem t_w3_dyn_rev_vtable_ref :
    decodePtrBytesNoForge true (.dynamic "Trait") 8
      (liveEnc 1 1 0x10 8 ++ (liveEnc 2 2 0x1122 8).reverse) =
      some (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8,
        .ptr { allocId := 2, offsetBytes := 0x2211000000000000 } 8]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w3_dyn_rev_vtable_ref

theorem t_w3_dyn_rev_vtable_raw :
    decodePtrBytesNoForge false (.dynamic "Trait") 8
      (liveEnc 1 1 0x10 8 ++ (liveEnc 2 2 0x1122 8).reverse) =
      some (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8,
        .ptr { allocId := 2, offsetBytes := 0x2211000000000000 } 8]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w3_dyn_rev_vtable_raw

theorem t_w3_dyn_swapped_halves_ref :
    decodePtrBytesNoForge true (.dynamic "Trait") 8 (liveEnc 2 2 0x40 8 ++ liveEnc 1 1 0x10 8) =
      some (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0x40 } 8,
        .ptr { allocId := 1, offsetBytes := 0x10 } 8]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w3_dyn_swapped_halves_ref

theorem t_w3_slice_prov_len_ref :
    decodePtrBytesNoForge true (.slice thinTy) 8 (liveEnc 1 1 0x10 8 ++ liveEnc 2 2 3 8) = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w3_slice_prov_len_ref

theorem t_w3_slice_swapped_raw :
    decodePtrBytesNoForge false (.slice thinTy) 8 (livePlain 3 8 ++ liveEnc 1 1 0x10 8) = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w3_slice_swapped_raw

theorem t_w3_str_intact_ref :
    decodePtrBytesNoForge true .str 8 (liveEnc 1 1 0x10 8 ++ livePlain 3 8) =
      some (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8, .scalar ⟨3, 8⟩]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w3_str_intact_ref

theorem t_w3_tag_dropped_on_decode :
    decodePtrBytesNoForge true thinTy 8 (liveEnc 5 9 0x40 8) =
      some (.ptr { allocId := 5, offsetBytes := 0x40 } 8) ∧
    ProvenancePtr.tag { allocId := 5, offsetBytes := 0x40 } = 5 :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w3_tag_dropped_on_decode

theorem t_w3_live_encode_writes_allocId_as_tag :
    encodeValueToBytes 16 layouts64 rawPtrTy (.ptr { allocId := 7, offsetBytes := 0x40 } 8) =
      some (liveEnc 7 7 0x40 8) ∧
    decodePtrBytesNoForge false thinTy 8 (liveEnc 7 7 0x40 8) =
      some (.ptr { allocId := 7, offsetBytes := 0x40 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w3_live_encode_writes_allocId_as_tag

theorem t_w3_mixed_tag_stripped_ref :
    decodePtrBytesNoForge true thinTy 8 (spliceBytes 4 (liveEnc 5 9 0x40 8) (liveEnc 5 10 0x40 8)) =
      none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w3_mixed_tag_stripped_ref

theorem t_w3_dyn_plain_vtable_ref_unsound :
    decodePtrBytesNoForge true (.dynamic "Trait") 8
      (liveEnc 1 1 0x10 8 ++ livePlain 0x1122 8) =
      some (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8, .scalar ⟨0x1122, 8⟩]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w3_dyn_plain_vtable_ref_unsound

theorem t_w3_dyn_encode_vtable_ptr_none :
    encodeValueToBytes 16 layouts64 dynRefTy
      (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8,
        .ptr { allocId := 2, offsetBytes := 0x1000 } 8]) = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w3_dyn_encode_vtable_ptr_none

theorem t_w3_raw_overlay_drops_tag_and_frag :
    overlayRawAbstractByteVals (encodeRawAbstractByteVals (liveEnc 5 9 0x40 8))
      (replicateUninitBytes 8) = some (liveEnc 5 5 0x40 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w3_raw_overlay_drops_tag_and_frag

theorem t_w1_decodeValueFromBytes_forges_prov :
    decodeValueFromBytes 16 layouts64 rawPtrTy (livePlain 0x20004 8) =
      some (.ptr { allocId := 2, offsetBytes := 4 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_decodeValueFromBytes_forges_prov

theorem t_w1_scalarLayout_32bit_none :
    decodeScalarLayoutBytesNoForge ptrScalarInit (liveEnc 1 1 0x11223344 4) = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_scalarLayout_32bit_none

theorem t_w4_global_misaligned_cross_reloc_unsound :
    (match globalAllocSliceToAbstractBytes globalTwoPtrsAlloc 1 8 with
      | some bs => decodePtrBytesNoForge true thinTy 8 bs
      | none => none) =
      some (.ptr { allocId := 1, offsetBytes := 0x1000000000000000 } 8) ∧
    (match globalAllocSliceToAbstractBytes globalTwoPtrsAlloc 4 8 with
      | some bs => decodePtrBytesNoForge false thinTy 8 bs
      | none => none) =
      some (.ptr { allocId := 1, offsetBytes := 0x0000001000000000 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w4_global_misaligned_cross_reloc_unsound

theorem t_w4_global_32bit_reloc_bleeds :
    globalAllocSliceToAbstractBytes
      { allocId := 100,
        bytes := [some 0x10, some 0, some 0, some 0, some 0x42, some 0, some 0, some 0],
        relocations := [(0, { allocId := 1, offsetBytes := 0x10 })],
        align := ⟨4⟩,
        mutability := .not } 4 4 =
      some [.init 0x42 (some (1, 1)), .init 0 (some (1, 1)),
            .init 0 (some (1, 1)), .init 0 (some (1, 1))] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w4_global_32bit_reloc_bleeds

theorem t_k_decode_bool_2_none :
    decodeTypedValueFromBytes 16 kLayouts tyBool [.init 2 none] = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_decode_bool_2_none

theorem t_k_decode_u8_2 :
    decodeTypedValueFromBytes 16 kLayouts tyU8 [.init 2 none] = some (.scalar ⟨2, 1⟩) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_decode_u8_2

theorem t_k_decode_maybeUninitBool_2 :
    decodeTypedValueFromBytes 16 kLayouts tyMUBool [.init 2 none] =
      some (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_decode_maybeUninitBool_2

theorem t_k_decode_nested_maybeUninitBool_2 :
    decodeTypedValueFromBytes 16 kLayouts tyMUMUBool [.init 2 none] =
      some (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_decode_nested_maybeUninitBool_2

theorem t_k_decode_unalignedBool_2_none :
    decodeTypedValueFromBytes 16 kLayouts tyUnalBool [.init 2 none] = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_decode_unalignedBool_2_none

theorem t_k_decode_unalignedBool_1 :
    decodeTypedValueFromBytes 16 kLayouts tyUnalBool [.init 1 none] =
      some (.aggregate 0 [.scalar ⟨1, 1⟩]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_decode_unalignedBool_1

theorem t_k_decode_unalignedBool_offset1 :
    (match sliceAbstractBytes [.init 7 none, .init 1 none, .init 9 none, .init 9 none] 1 1 with
      | some bs => decodeTypedValueFromBytes 16 kLayouts tyUnalBool bs
      | none => none) = some (.aggregate 0 [.scalar ⟨1, 1⟩]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_decode_unalignedBool_offset1

theorem t_k_decode_maybeUninitUnaligned_2 :
    decodeTypedValueFromBytes 16 kLayouts tyMUUnal [.init 2 none] =
      some (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_decode_maybeUninitUnaligned_2

theorem t_k_decode_char_surrogate :
    decodeTypedValueFromBytes 16 kLayouts tyChar (livePlain 0xD800 4) = none ∧
    decodeTypedValueFromBytes 16 kLayouts tyU32 (livePlain 0xD800 4) = some (.scalar ⟨0xD800, 4⟩) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_decode_char_surrogate

theorem t_k_copy_u8arr_to_maybeUninitBool :
    stepOutcome (copyActive tyU8A1 tyMUBool u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.unit, .scalar ⟨2, 1⟩]))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_copy_u8arr_to_maybeUninitBool

theorem t_k_copy_u8arr_to_nestedMaybeUninitBool :
    stepOutcome (copyActive tyU8A1 tyMUMUBool u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.unit, .scalar ⟨2, 1⟩]))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_copy_u8arr_to_nestedMaybeUninitBool

theorem t_k_copy_u8arr_to_u8arr :
    stepOutcome (copyActive tyU8A1 tyU8A1 u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.scalar ⟨2, 1⟩]))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_copy_u8arr_to_u8arr

theorem t_k_copy_maybeUninit_to_maybeUninit :
    stepOutcome (copyActive tyMUBool tyMUBool muBool2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.unit, .scalar ⟨2, 1⟩])) muBool2) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_copy_maybeUninit_to_maybeUninit

theorem t_k_copy_union_to_nonunion :
    stepOutcome (copyActive tyMUBool tyU8A1 muBool2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.scalar ⟨2, 1⟩])) muBool2) [] ∧
    stepOutcome (copyActive tyMUBool tyBool muBool2 .uninit) = .ub ∧
    stepOutcome (copyActive tyMUBool tyUnalBool muBool2 .uninit) = .ub :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_copy_union_to_nonunion

theorem t_k_copy_u8arr_to_bool_premature_ub :
    stepOutcome (copyActive tyU8A1 tyBool u8Arr2 .uninit) = .ub :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_copy_u8arr_to_bool_premature_ub

theorem t_k_copy_u8_to_bool_premature_ub :
    stepOutcome (copyActive tyU8 tyBool u8Scalar2 .uninit) = .ub :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_copy_u8_to_bool_premature_ub

theorem t_k_copy_u8arr_to_unalignedBool :
    stepOutcome (copyActive tyU8A1 tyUnalBool u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.scalar ⟨2, 1⟩]))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_copy_u8arr_to_unalignedBool

theorem t_k_copy_u8_to_unalignedBool_shape_vs_typed :
    stepOutcome (copyActive tyU8 tyUnalBool u8Scalar2 .uninit) =
      .step (activeLocals (.init (.scalar ⟨2, 1⟩)) u8Scalar2) [] ∧
    stepOutcome (copyActiveEx tyU8 tyUnalBool tyPtrU8 tyPtrUnalBool 0 0 1 u8Scalar2 .uninit) = .ub :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_copy_u8_to_unalignedBool_shape_vs_typed

theorem t_k_copy_u8arr_to_maybeUninitUnaligned :
    stepOutcome (copyActive tyU8A1 tyMUUnal u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.unit, .scalar ⟨2, 1⟩]))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_copy_u8arr_to_maybeUninitUnaligned

theorem t_k_copy_subplace_multi_audit :
    stepOutcome (copyActiveEx tyU8A2 tyBoolA2 tyPtrU8 tyPtrU8 0 0 2 u8Arr12 .uninit) = .unsupported ∧
    stepOutcome (copyActiveEx tyU8A4 tyBool tyPtrU8 tyPtrU8 1 0 1 u8Arr4Bad .uninit) = .unsupported ∧
    stepOutcome (copyActiveEx tyU8A4 tyUnalBool tyPtrU8 tyPtrU8 1 0 1 u8Arr4Bad .uninit) =
      .unsupported ∧
    stepOutcome (copyActiveEx tyU8A4 tyUnalBool tyPtrU8 tyPtrU8 1 0 1 u8Arr4Ok .uninit) =
      .unsupported ∧
    stepOutcome (copyActiveEx tyU8A4 tyBool tyPtrU8 tyPtrU8 1 0 1 u8Arr4Ok .uninit) =
      .step (activeLocalsAt 1 0 (.init (.scalar ⟨1, 1⟩)) u8Arr4Ok) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_copy_subplace_multi_audit

theorem t_k_gap_unalignedBool_field_reads_2 :
    copyThenRead tyU8A1 tyUnalBool u8Arr2 [.field 0 tyBool] = .ok (.scalar ⟨2, 1⟩) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_gap_unalignedBool_field_reads_2

theorem t_k_gap_unalignedBool_whole_reads_2 :
    copyThenRead tyU8A1 tyUnalBool u8Arr2 [] = .ok (.aggregate 0 [.scalar ⟨2, 1⟩]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_gap_unalignedBool_whole_reads_2

theorem t_k_gap_maybeUninitUnaligned_assume_init :
    copyThenRead tyU8A1 tyMUUnal u8Arr2 [.field 1 tyUnalBool] =
      .ok (.scalar ⟨2, 1⟩) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_gap_maybeUninitUnaligned_assume_init

theorem t_k_maybeUninitBool_assume_init_ub :
    copyThenRead tyU8A1 tyMUBool u8Arr2 [.field 1 tyBool] = .ub :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_maybeUninitBool_assume_init_ub

theorem t_k_maybeUninitUnaligned_inner_field_ub :
    copyThenRead tyU8A1 tyMUUnal u8Arr2 [.field 1 tyUnalBool, .field 0 tyBool] = .ub :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_maybeUninitUnaligned_inner_field_ub

theorem t_k_bool_local_holding_2_reads_ok :
    readOutcome (evalOperand [.init .unit, .uninit, .init (.scalar ⟨2, 1⟩)] (.copy (lc 2)) [] []
      kLayouts [] [decl tyUnit, decl tyU8A1, decl tyBool] []) = .ok (.scalar ⟨2, 1⟩) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_bool_local_holding_2_reads_ok

theorem t_k_gap_foreign_u8_to_bool_stores_2 :
    stepOutcome (copyForeign tyU8 tyBool u8Scalar2 .uninit) =
      .step (foreignActive u8Scalar2) [[.init .unit, .init (.scalar ⟨2, 1⟩)]] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_gap_foreign_u8_to_bool_stores_2

theorem t_k_gap_foreign_u8arr_to_bool_stores_array :
    stepOutcome (copyForeign tyU8A1 tyBool u8Arr2 .uninit) =
      .step (foreignActive u8Arr2) [[.init .unit, .init (.aggregate 0 [.scalar ⟨2, 1⟩])]] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_gap_foreign_u8arr_to_bool_stores_array

theorem t_k_foreign_u8_to_maybeUninitBool :
    stepOutcome (copyForeign tyU8 tyMUBool u8Scalar2 .uninit) =
      .step (foreignActive u8Scalar2) [[.init .unit, .init (.scalar ⟨2, 1⟩)]] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_foreign_u8_to_maybeUninitBool

theorem t_proto_projects_to_liveEnc :
    (encodePtrBytesProto ⟨1, 1, 0x1122334455667788⟩ 8).map AbstractByteProto.toLive08 =
      liveEnc 1 1 0x1122334455667788 8 :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.proto_projects_to_liveEnc

theorem t_k_gap_union_to_ptr_forges_provenance :
    stepOutcome (copyActiveEx tyMUPtr tyRawU8 tyPtrRawU8 tyPtrRawU8 0 0 1 muPtrPlain .uninit) =
      .step (activeLocals (.init (.ptr { allocId := 2, offsetBytes := 4 } 8)) muPtrPlain) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_gap_union_to_ptr_forges_provenance

theorem t_k_copy_usize_to_ptr_no_forge :
    stepOutcome (copyActiveEx tyUsize tyRawU8 tyPtrRawU8 tyPtrRawU8 0 0 1
      (.init (.scalar ⟨0x20004, 8⟩)) .uninit) =
      .step (activeLocals (.init (.scalar ⟨0x20004, 8⟩)) (.init (.scalar ⟨0x20004, 8⟩))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_copy_usize_to_ptr_no_forge

theorem t_k_gap_singleDirect_usize_to_ptr_forges_provenance :
    stepOutcome (copyActiveEx tyUsize tyRawU8 tyPtrUsize tyPtrRawU8 0 0 1
      (.init (.scalar ⟨0x20004, 8⟩)) .uninit) =
      .step (activeLocals (.init (.ptr { allocId := 2, offsetBytes := 4 } 8))
        (.init (.scalar ⟨0x20004, 8⟩))) [] ∧
    stepOutcome (copyActiveEx tyUsize tyRefU8 tyPtrUsize tyPtrRefU8 0 0 1
      (.init (.scalar ⟨0x20004, 8⟩)) .uninit) =
      .step (activeLocals (.init (.ptr { allocId := 2, offsetBytes := 4 } 8))
        (.init (.scalar ⟨0x20004, 8⟩))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_gap_singleDirect_usize_to_ptr_forges_provenance

theorem t_k_copy_subplaceMulti_u8arr8_to_ptr_unsupported :
    stepOutcome (copyActiveEx tyU8A8 tyRawU8 tyPtrU8 tyPtrU8 0 0 8 u8Arr8Addr .uninit) =
      .unsupported ∧
    stepOutcome (copyActiveEx tyU8A8 tyRefU8 tyPtrU8 tyPtrU8 0 0 8 u8Arr8Addr .uninit) =
      .unsupported :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_copy_subplaceMulti_u8arr8_to_ptr_unsupported

theorem t_k_gap_ptr_to_usize_keeps_provenance :
    stepOutcome (copyActiveEx tyRawU8 tyUsize tyPtrRawU8 tyPtrRawU8 0 0 1
      (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8)) .uninit) =
      .step (activeLocals (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8))
        (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8))) [] ∧
    readOutcome (evalOperand [.init .unit, .uninit,
        .init (.ptr { allocId := 7, offsetBytes := 0x40 } 8)] (.copy (lc 2)) [] [] kLayouts []
      [decl tyUnit, decl tyUnit, decl tyUsize] []) =
      .ok (.ptr { allocId := 7, offsetBytes := 0x40 } 8) ∧
    stepOutcome (copyActiveEx tyRawU8 tyUsize tyPtrRawU8 tyPtrUsize 0 0 1
      (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8)) .uninit) =
      .step (activeLocals (.init (.scalar ⟨0x40, 8⟩))
        (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8))) [] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_gap_ptr_to_usize_keeps_provenance

theorem t_k_copy_ptr_bytewise_unsupported :
    stepOutcome (copyActiveEx tyRawU8 tyU8A8 tyPtrU8 tyPtrU8 0 0 8
      (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8)) u8Arr8Zero) = .unsupported ∧
    stepOutcome (copyActiveEx tyRawU8 tyU8A4 tyPtrU8 tyPtrU8 0 0 4
      (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8)) .uninit) = .unsupported ∧
    stepOutcome (copyActiveEx tyRawU8 tyRawU8 tyPtrU8 tyPtrU8 0 0 8
      (.init (.ptr { allocId := 7, offsetBytes := 0x40 } 8)) .uninit) = .unsupported :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_copy_ptr_bytewise_unsupported

theorem t_k_gap_foreign_usize_to_ptr_forges_provenance :
    stepOutcome (copyForeignEx tyUsize tyRawU8 tyPtrUsize tyPtrRawU8
      (.init (.scalar ⟨0x20004, 8⟩)) .uninit) =
      .step (foreignActive (.init (.scalar ⟨0x20004, 8⟩)))
        [[.init .unit, .init (.ptr { allocId := 2, offsetBytes := 4 } 8)]] :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.k_gap_foreign_usize_to_ptr_forges_provenance

theorem t_w1_encode_32bit_ptr_none :
    encodeValueToBytes 16 layouts32 rawPtrTy (.ptr { allocId := 1, offsetBytes := 0x10 } 4) =
      none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w1_encode_32bit_ptr_none

theorem t_w3_wide_swapped_halves_matrix :
    decodePtrBytesNoForge false .str 8 (livePlain 3 8 ++ liveEnc 1 1 0x10 8) = none ∧
    decodePtrBytesNoForge true .str 8 (livePlain 3 8 ++ liveEnc 1 1 0x10 8) = none ∧
    decodePtrBytesNoForge true (.slice thinTy) 8 (livePlain 3 8 ++ liveEnc 1 1 0x10 8) = none ∧
    decodePtrBytesNoForge true .str 8 (liveEnc 1 1 0x10 8 ++ liveEnc 2 2 3 8) = none ∧
    decodePtrBytesNoForge false (.dynamic "Trait") 8 (liveEnc 2 2 0x40 8 ++ liveEnc 1 1 0x10 8) =
      some (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0x40 } 8,
        .ptr { allocId := 1, offsetBytes := 0x10 } 8]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w3_wide_swapped_halves_matrix

theorem t_w4_const_indirect_forges_prov :
    evalConstValue (.indirect 101 0) rawPtrTy [globalPlainAddrAlloc] layouts64 =
      some (.ptr { allocId := 2, offsetBytes := 4 } 8) ∧
    evalConstValue (.indirect 101 0) tyRefU8 [globalPlainAddrAlloc] layouts64 =
      some (.ptr { allocId := 2, offsetBytes := 4 } 8) ∧
    evalConstValue (.slice (.int ⟨0x20004, 8⟩) 5)
        { kind := .rawPtr .not (.slice thinTy), layoutIdx := 0 } [] layouts64 =
      some (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 4 } 8, .scalar ⟨5, 8⟩]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w4_const_indirect_forges_prov

theorem t_w4_decodeValueFromBytes_single_mixed_byte_unsound :
    decodeValueFromBytes 16 layouts64 rawPtrTy
        ([.init 0x10 (some (1, 1))] ++ livePlain 0 7) =
      some (.ptr { allocId := 1, offsetBytes := 0x10 } 8) ∧
    decodeValueFromBytes 16 layouts64 tyRefU8
        ([.init 0x10 (some (1, 1))] ++ livePlain 0 7) =
      some (.ptr { allocId := 1, offsetBytes := 0x10 } 8) ∧
    decodeValueFromBytes 16 layouts64 tyRefU8
        (spliceBytes 1 (liveEnc 1 1 0x10 8) (liveEnc 2 2 0x200 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x210 } 8) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w4_decodeValueFromBytes_single_mixed_byte_unsound

theorem t_w5_byteCast_transmute_audit :
    byteCastOutcome tyMUPtr tyRefU8 muPtrRevVal =
      .ok (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) ∧
    byteCastOutcome tyMUPtr tyRefU8 muPtrSpliceVal =
      .ok (.ptr { allocId := 1, offsetBytes := 256 } 8) ∧
    byteCastOutcome tyUsize tyRawU8 (.scalar ⟨0x20004, 8⟩) = .ok (.scalar ⟨0x20004, 8⟩) ∧
    byteCastOutcome tyUsize tyRefU8 (.scalar ⟨0x20004, 8⟩) = .ub ∧
    byteCastOutcome tyRawU8 tyUsize (.ptr { allocId := 7, offsetBytes := 0x40 } 8) = .ub ∧
    byteCastOutcome tyU8 tyBool (.scalar ⟨2, 1⟩) = .ub ∧
    byteCastOutcome tyU8 tyUnalBool (.scalar ⟨2, 1⟩) = .ub ∧
    byteCastOutcome tyU8 tyMUBool (.scalar ⟨2, 1⟩) =
      .ok (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]]) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w5_byteCast_transmute_audit

theorem t_w5_enum_multiple_allows_prov_bytes :
    decodeTypedValueFromBytes 16 enumTagLayouts tyEnumTag2 [.init 1 (some (1, 1))] =
      some (.aggregate 1 []) ∧
    decodeTypedValueFromBytes 16 kLayouts tyBool [.init 1 (some (1, 1))] = none ∧
    decodeTypedValueFromBytes 16 kLayouts tyU8 [.init 1 (some (1, 1))] = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.LiveV08.w5_enum_multiple_allows_prov_bytes

end RestateLiveV08

namespace RestateThreeWay

open Anneal.Proto.Ucg558PtrByteCoherenceProto

theorem t_mr_intact :
    MiniRustSpec.Interp.decodePtr (mrEnc 1 0x1122) =
      .ok (some { addr := 0x1122, provenance := some (mrProv 1) }) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.mr_intact

theorem t_mr_encodePtr_concrete :
    MiniRustSpec.Interp.encodePtr { addr := 0x1122, provenance := some (mrProv 1) } =
      .ok (mrEnc 1 0x1122) ∧
    (MiniRustSpec.Interp.encodePtr { addr := 0x1122, provenance := some (mrProv 1) }).bind
        MiniRustSpec.Interp.decodePtr =
      .ok (some { addr := 0x1122, provenance := some (mrProv 1) }) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.mr_encodePtr_concrete

theorem t_mr_w1_rev8 :
    MiniRustSpec.Interp.decodePtr (mrEnc 1 0x1122334455667788).reverse =
      .ok (some { addr := 0x8877665544332211, provenance := none }) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.mr_w1_rev8

theorem t_mr_w1_rev8_zero :
    MiniRustSpec.Interp.decodePtr (mrEnc 1 0).reverse =
      .ok (some { addr := 0, provenance := none }) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.mr_w1_rev8_zero

theorem t_mr_w1_rev4 :
    mrDecodedProv (mrEnc4 1 0x11223344).reverse = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.mr_w1_rev4

theorem t_mr_w1_swap01 :
    MiniRustSpec.Interp.decodePtr (swapFirstTwo (mrEnc 1 0x1122)) =
      .ok (some { addr := 0x2211, provenance := none }) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.mr_w1_swap01

theorem t_mr_w1_dup0 :
    MiniRustSpec.Interp.decodePtr (dupFirstByte (mrEnc 1 0x1122)) =
      .ok (some { addr := 0x2222222222222222, provenance := none }) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.mr_w1_dup0

theorem t_mr_w2_splice_0_256 :
    MiniRustSpec.Interp.decodePtr (spliceBytes 1 (mrEnc 1 0) (mrEnc 1 256)) =
      .ok (some { addr := 256, provenance := some (mrProv 1) }) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.mr_w2_splice_0_256

theorem t_mr_w2_splice_0_4 :
    MiniRustSpec.Interp.decodePtr (spliceBytes 1 (mrEnc 1 0) (mrEnc 1 4)) =
      .ok (some { addr := 0, provenance := some (mrProv 1) }) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.mr_w2_splice_0_4

theorem t_mr_w2_splice_10_14 :
    MiniRustSpec.Interp.decodePtr (spliceBytes 1 (mrEnc 1 0x10) (mrEnc 1 0x14)) =
      .ok (some { addr := 0x10, provenance := some (mrProv 1) }) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.mr_w2_splice_10_14

theorem t_miri_intact :
    inspectFragmentsMirror none (miriFrags (encodePtrBytesProto ⟨1, 1, 0x1122⟩ 8)) =
      .ok (some (1, 1)) :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.miri_intact

theorem t_miri_w1_rev8 :
    inspectFragmentsMirror none
      (miriFrags (encodePtrBytesProto ⟨1, 1, 0x1122334455667788⟩ 8).reverse) = .ok none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.miri_w1_rev8

theorem t_miri_w1_rev8_zero :
    inspectFragmentsMirror none (miriFrags (encodePtrBytesProto ⟨1, 1, 0⟩ 8).reverse) =
      .ok none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.miri_w1_rev8_zero

theorem t_miri_w1_rev4 :
    inspectFragmentsMirror none (miriFrags (encodePtrBytesProto ⟨1, 1, 0x11223344⟩ 4).reverse) =
      .ok none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.miri_w1_rev4

theorem t_miri_w1_swap01 :
    inspectFragmentsMirror none (miriFrags (swapFirstTwo (encodePtrBytesProto ⟨1, 1, 0x1122⟩ 8))) =
      .ok none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.miri_w1_swap01

theorem t_miri_w1_dup0 :
    inspectFragmentsMirror none (miriFrags (dupFirstByte (encodePtrBytesProto ⟨1, 1, 0x1122⟩ 8))) =
      .ok none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.miri_w1_dup0

theorem t_miri_w2_splice_0_256 :
    inspectFragmentsMirror none (miriFrags
      (spliceBytes 1 (encodePtrBytesProto ⟨1, 1, 0⟩ 8) (encodePtrBytesProto ⟨1, 1, 256⟩ 8))) =
      .ok none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.miri_w2_splice_0_256

theorem t_miri_w2_splice_0_4 :
    inspectFragmentsMirror none (miriFrags
      (spliceBytes 1 (encodePtrBytesProto ⟨1, 1, 0⟩ 8) (encodePtrBytesProto ⟨1, 1, 4⟩ 8))) =
      .ok none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.miri_w2_splice_0_4

theorem t_miri_w2_splice_10_14 :
    inspectFragmentsMirror none (miriFrags
      (spliceBytes 1 (encodePtrBytesProto ⟨1, 1, 0x10⟩ 8) (encodePtrBytesProto ⟨1, 1, 0x14⟩ 8))) =
      .ok none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.miri_w2_splice_10_14

theorem t_miri_wildcard_semantics :
    inspectFragmentsMirror (some (0, 0))
      [some ⟨0, (0, 0), imageVec8 0⟩, some ⟨1, (1, 1), imageVec8 0x1122⟩] = .ok (some (1, 1)) ∧
    inspectFragmentsMirror (some (0, 0)) [some ⟨5, (0, 0), imageVec8 0⟩] = .ok (some (0, 0)) ∧
    inspectFragmentsMirror (none : Option (Nat × Nat)) [] = .missingWildcard :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.miri_wildcard_semantics

theorem t_miri_mismatch_semantics :
    inspectFragmentsMirror none [some ⟨1, (1, 1), imageVec8 0⟩] = .ok none ∧
    inspectFragmentsMirror none
      [some ⟨0, (1, 1), imageVec8 0⟩, some ⟨1, (1, 1), imageVec8 1⟩] = .ok none ∧
    inspectFragmentsMirror none
      [some ⟨0, (1, 1), imageVec8 0⟩, some ⟨1, (1, 2), imageVec8 0⟩] = .ok none ∧
    inspectFragmentsMirror none [some ⟨0, (1, 1), imageVec8 0⟩, none] = .ok none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.miri_mismatch_semantics

theorem t_w2_five_way :
    LiveV06.decodePtrBytesNoForgeLive true 8
        (spliceBytes 1 (LiveV06.liveEnc 1 1 0 8) (LiveV06.liveEnc 1 1 256 8)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 8) ∧
    LiveV08.decodePtrBytesNoForgeLive true 8
        (spliceBytes 1 (LiveV08.liveEnc 1 1 0 8) (LiveV08.liveEnc 1 1 256 8)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 8) ∧
    MiniRustSpec.Interp.decodePtr (spliceBytes 1 (mrEnc 1 0) (mrEnc 1 256)) =
      .ok (some { addr := 256, provenance := some (mrProv 1) }) ∧
    inspectFragmentsMirror none (miriFrags
      (spliceBytes 1 (encodePtrBytesProto ⟨1, 1, 0⟩ 8) (encodePtrBytesProto ⟨1, 1, 256⟩ 8))) =
      .ok none ∧
    decodePtrBytesNoForgeProto true .thin 8
      (spliceBytes 1 (encodePtrBytesProto ⟨1, 1, 0⟩ 8) (encodePtrBytesProto ⟨1, 1, 256⟩ 8)) =
      none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.w2_five_way

theorem t_w1_five_way_zero_rev :
    LiveV06.decodePtrBytesNoForgeLive true 8 (LiveV06.liveEnc 1 1 0 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0 } 8) ∧
    LiveV08.decodePtrBytesNoForgeLive true 8 (LiveV08.liveEnc 1 1 0 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0 } 8) ∧
    MiniRustSpec.Interp.decodePtr (mrEnc 1 0).reverse =
      .ok (some { addr := 0, provenance := none }) ∧
    inspectFragmentsMirror none (miriFrags (encodePtrBytesProto ⟨1, 1, 0⟩ 8).reverse) = .ok none ∧
    decodePtrBytesNoForgeProto true .thin 8 (encodePtrBytesProto ⟨1, 1, 0⟩ 8).reverse = none :=
  Anneal.Proto.Ucg558PtrByteCoherenceProto.w1_five_way_zero_rev

end RestateThreeWay

/-! ## 4. Mechanical axiom audit -/

/-! Audits every declaration of `Anneal.Proto.Ucg558PtrByteCoherenceProto` and every
declaration of this test namespace: no `unsafe` declaration, and every axiom used lies in
`{propext, Classical.choice, Quot.sound}` (no `sorryAx`, no `Lean.ofReduceBool`, no
`_native.*`). Non-vacuity: every user theorem of the module must be reachable from the
declarations of this file. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ns := `Anneal.Proto.Ucg558PtrByteCoherenceProto
  let userParents : List Name := [ns, ns ++ `LiveV06, ns ++ `LiveV08]
  let some modIdx := env.getModuleIdx? `Anneal.Proto.Ucg558PtrByteCoherenceProto
    | throwError "prototype module not imported"
  let mut audited : Nat := 0
  let mut auditedSet : NameSet := {}
  let mut moduleThms : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some modIdx then
      if ci.isUnsafe then throwError "unsafe declaration: {n}"
      let axs ← collectAxioms n
      for a in axs do
        unless allowed.contains a do
          throwError "{n} depends on disallowed axiom {a}"
      audited := audited + 1
      auditedSet := auditedSet.insert n
      if ci matches .thmInfo _ then
        if userParents.contains n.getPrefix then
          moduleThms := moduleThms.push n
  if moduleThms.size < 150 then
    throwError "audited only {moduleThms.size} module theorems (expected ≥ 150)"
  let mut testThms : Nat := 0
  let mut reached : NameSet := {}
  let mut work : Array Name := #[]
  for (n, ci) in env.constants.map₂.toList do
    if (`Anneal.Ucg558PtrByteCoherenceProtoTests).isPrefixOf n then
      if ci.isUnsafe then throwError "unsafe declaration: {n}"
      let axs ← collectAxioms n
      for a in axs do
        unless allowed.contains a do
          throwError "{n} depends on disallowed axiom {a}"
      if ci matches .thmInfo _ then testThms := testThms + 1
      for c in ci.getUsedConstantsAsSet do
        if auditedSet.contains c && !reached.contains c then
          reached := reached.insert c
          work := work.push c
  while !work.isEmpty do
    let c := work.back!
    work := work.pop
    if let some ci := env.find? c then
      for d in ci.getUsedConstantsAsSet do
        if auditedSet.contains d && !reached.contains d then
          reached := reached.insert d
          work := work.push d
  let unreached := moduleThms.filter (fun n => !reached.contains n)
  unless unreached.isEmpty do
    throwError "module theorems not instantiated by any test: {unreached.toList}"
  logInfo m!"axiom audit passed: {audited} module declarations ({moduleThms.size} theorems, \
    all instantiated), {testThms} test theorems"

end Anneal.Ucg558PtrByteCoherenceProtoTests
