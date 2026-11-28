/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import MiniRustSpec.Interp
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import Trusted.Rustc.V2026_06_01.MirSemantics.Statements
import Trusted.Rustc.V2026_08_01.MirSemantics.Places
import Trusted.Rustc.V2026_08_01.MirSemantics.Statements

/-!
# Episode 2 Dual-Authority Correspondence (`MiniRustSpec` Authority):
# pointer-byte fragment coherence (`UCG#558` / `rust#148259`) and read-time validity (`Kani#5205`)

Correspondence between the pointer-byte codec of
`Trusted.Rustc.V2026_{06,08}_01.MirSemantics` (`encodePtrBytes`,
`encodeUntypedValueToBytes`, `abstractBytesCoherentPtrProv?`,
`decodePtrBytesNoForge`, `decodeScalarLayoutBytesNoForge`,
`decodeTypedValueFromBytes`, the union raw-byte carrier
`encodeRawAbstractByteVal` / `decodeRawAbstractByteVals?`) and the MiniRust
representation relation of `MiniRustSpec.Interp` (`encodePtr`, `encodePtrBytes`,
`decodePtr`, `decodePtrProvenance`, and the memory-polymorphic `encodePtrM`,
`encodePtrBytesM`, `decodePtrM`, `decodePtrProvenanceM`, `decodeWidePtrM`,
`Type.decode` / `Type.decodeM`) across **both** `BasicMemory<x86_64>` and
`TreeBorrowsMemory<x86_64>`, in lockstep for `V2026_06_01` and `V2026_08_01`.

## The fragment projection

A `Trusted` `PtrByteFrag { allocId, tag, byteIdx, origOffset, ptrBytes }` is
projected to the MiniRust `ProvenanceFrag { provenance, position := byteIdx }`
by `projFrag pv` for a provenance embedding `pv : Nat → Nat → M::Provenance`
(`bmProv` for `BasicMemory`, which has no borrow tags, and the injective
`tbProv` for `TreeBorrowsMemory`). The projection **forgets** `origOffset` and
`ptrBytes`: MiniRust's `ProvenanceFrag` records only the provenance and the
position of the byte inside its pointer.

## Theorem surface (each section is generated identically for `V06` and `V08`)

1. **Exact encoding and intact round trips.** `proj_encodePtrBytes`,
   `encodePtrM_proj`, `encodePtr_proj`, `proj_plain_bytes`,
   `decodePtrM_proj_encodePtrBytes`, `thinDecode_encodePtrBytes`,
   `decodePtrBytesNoForge_thin`, `scalarLayoutPtr_coherent`,
   `encodeUntyped_ptr`, `rawCarrier_roundtrip`, `rawCarrier_ptr_roundtrip`.
2. **Positional coherence (`UCG#558` W1).** `coherent?_eq_some_iff` and
   `mrProvM_eq_some_iff` characterize both authorities exactly;
   `coherent_decode_agreement` is the `Trusted → MiniRust` soundness law;
   `permuted_strips_trusted` / `permuted_strips_minirust` (any byte at a
   position other than its own), `reversal_strips`, `swap01_strips`,
   `dupHead_strips`, `mixed_provenance_strips_*`, `missing_provenance_strips_*`,
   and `uninit_rejected_*` are the shared stripping laws.
3. **Offset splices (`UCG#558` W2 / `rust#148259`).**
   `offset_splice_trusted_strips` and `offset_splice_minirust_retains` are the
   two halves of the strict refinement; `trusted_retains_implies_minirust_retains`
   is the directional refinement and `converse_gap_iff` characterizes exactly
   when the converse fails (some pair of fragments disagrees on `origOffset` or
   `ptrBytes`, or the fragment width is not the stream length).
4. **Wide pointers, `Kani#5205`.** `decodePtrBytesNoForge_slice`,
   `slice_meta_with_provenance_rejected`, the three-way wide-pointer witnesses
   (`w_wide_*`), `minirust_bool_invalid`, and the `Kani#5205` witnesses
   (`w_kani5205_*`).
5. **Lockstep parity** (`Parity` section) and **non-vacuity** (`*_instance`
   theorems and `w_*` witnesses, all kernel-checked).

## Scoped divergences (each pinned by a kernel-checked witness)

* `DIV-MR-OFFSET-SPLICE` (`w_offset_splice_*`): vendored MiniRust retains
  provenance on a same-provenance splice of `p` and `p + k` because its
  `ProvenanceFrag` carries no original pointer bytes; `Trusted` strips it, as
  Miri / CTFE do (`rust#148259`). `Trusted` is a strict refinement
  (`trusted_retains_implies_minirust_retains`, `converse_gap_iff`).
* `DIV-MR-BASIC-TAG` (`w_basic_memory_tag_blind`): `BasicMemory` provenance is
  `(AllocId, ())`, so two `Trusted` fragments of one allocation with different
  borrow tags project to the same MiniRust provenance. `TreeBorrowsMemory`
  provenance (`tbProv`) is injective and has no such gap.
* `DIV-MR-PTR2INT` (`w_wide_swapped_halves`, `slice_meta_with_provenance_rejected`):
  MiniRust `Type::Int` decoding ignores provenance (a pointer-to-integer
  transmute strips provenance), so a slice length read from pointer bytes is
  accepted; `Trusted` pins `Ptr2IntTransmutePolicy.strictUcg630Ub` and rejects
  provenance-bearing slice / `str` metadata.
* `DIV-MR-CHAR` (`w_kani5205_char`, `kani5205_char_divergence`) vs. **exact `Type::Enum`
  correspondence** (`minirustCharType`, `kani5205_char_correspondence_M`): MiniRust has no
  primitive `Type::Char` constructor (so `Type::Int(u32)` accepts all `c < 2^32`, including
  surrogates `0xD800 ..= 0xDFFF`); however, MiniRust's standard `Type::Enum` + `Discriminator::Branch`
  encoding of Rust `char` (`[0, 0xD800) ∪ [0xE000, 0x110000)` with fallback `.Invalid`) matches
  `Trusted` `validateValueForTy?` and `decodeTypedValueFromBytes` biconditionally across **every**
  `c < 2^32` and both `BasicMemory` and `TreeBorrowsMemory` (`kani5205_char_correspondence_M`).
* `DIV-MR-DYN-VTABLE` (`w_wide_dyn`): at the representation level MiniRust
  decodes an incoherent vtable pointer to a provenance-free pointer and rejects
  it only in `check_value` through `Machine::vtable_from_ptr`; `Trusted` has no
  vtable table in its IR / `Memory` and rejects an incoherent `&dyn` vtable
  half at decode time.

This module imports no `Anneal.*`, `Miri.*`, or `LeanMiriSpec.*` module
(verified by the trailing `#assert_ptr_byte_coherence_mr_audit`).
-/

set_option Elab.async false

namespace MiniRustSpec.PtrByteCoherenceMR

open MiniRustSpec

/-! ## Part 0. Version-independent MiniRust laws -/

section Shared

theorem nat_beq_iff (a b : Nat) : Nat.beq a b = true ↔ a = b := by
  constructor
  · exact Nat.eq_of_beq_eq_true
  · intro h
    subst h
    induction a with
    | zero => rfl
    | succ n ih => exact ih

theorem ite_of_pos {c : Prop} [inst : Decidable c] {α : Type} {t e : α} (hc : c) :
    (if c then t else e) = t := by
  cases inst with
  | isTrue _ => rfl
  | isFalse h => exact absurd hc h

theorem ite_of_neg {c : Prop} [inst : Decidable c] {α : Type} {t e : α} (hc : ¬ c) :
    (if c then t else e) = e := by
  cases inst with
  | isTrue h => exact absurd h hc
  | isFalse _ => rfl

theorem u8_ofNat_toNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by
  simp [UInt8.toNat_ofNat']

theorem u8_ofNat_mod (n : Nat) : UInt8.ofNat (n % 256) = UInt8.ofNat n := by
  apply UInt8.toNat_inj.mp
  rw [u8_ofNat_toNat, u8_ofNat_toNat, Nat.mod_mod]

/-- `BasicMemory` provenance of a `Trusted` `(allocId, tag)` pair. `BasicMemory`
provenance is `(AllocId, ())`: it has no borrow tags. -/
def bmProv (a _t : Nat) : Gen.Memory.Provenance Interp.BM :=
  ((⟨(a : Int)⟩, ()) : Interp.Prov)

/-- `TreeBorrowsMemory` provenance of a `Trusted` `(allocId, tag)` pair: the
allocation and the one-step tree path `[tag]`. -/
def tbProv (a t : Nat) : Gen.Memory.Provenance Interp.TBM :=
  ((⟨(a : Int)⟩, [(t : Int)]) : Gen.TreeBorrowsProvenance)

theorem bmProv_eq_iff (a t a' t' : Nat) : bmProv a t = bmProv a' t' ↔ a = a' := by
  unfold bmProv
  constructor
  · intro h
    injection h with h1 _
    injection h1 with h1
    omega
  · intro h
    subst h
    rfl

theorem tbProv_inj (a t a' t' : Nat) (h : tbProv a t = tbProv a' t') : a = a' ∧ t = t' := by
  unfold tbProv at h
  injection h with h1 h2
  injection h1 with h1
  injection h2 with h2 _
  omega

/-- MiniRust positional coherence: byte `i` of `bs` (the first one having index
`idx`) is initialized and carries the fragment `{ provenance := p, position := idx + i }`. -/
def MrCoh {P : Type} (p : P) : Nat → List (Gen.AbstractByte P) → Prop
  | _, [] => True
  | idx, b :: rest => (∃ v, b = .Init v (some ⟨p, (idx : Int)⟩)) ∧ MrCoh p (idx + 1) rest

theorem mrCoh_iff_get {P : Type} (p : P) :
    ∀ (bs : List (Gen.AbstractByte P)) (idx : Nat),
      MrCoh p idx bs ↔
        ∀ (i : Nat) (b : Gen.AbstractByte P), bs[i]? = some b →
          ∃ v, b = Gen.AbstractByte.Init v (some ⟨p, ((idx + i : Nat) : Int)⟩)
  | [], idx => by
      constructor
      · intro _ i b hb
        cases hb
      · intro _
        trivial
  | x :: rest, idx => by
      have ih := mrCoh_iff_get p rest (idx + 1)
      constructor
      · intro h i b hb
        cases i with
        | zero =>
            have hx : some x = some b := hb
            injection hx with hx
            subst hx
            exact h.1
        | succ j =>
            have hb' : rest[j]? = some b := hb
            have := (ih.mp h.2) j b hb'
            have e : idx + 1 + j = idx + (j + 1) := by omega
            rw [e] at this
            exact this
      · intro h
        refine And.intro (h 0 x rfl) (ih.mpr ?_)
        intro j b hb
        have := h (j + 1) b hb
        have e : idx + (j + 1) = idx + 1 + j := by omega
        rw [e] at this
        exact this

/-- Exact characterization of the provenance fold of `decode_ptr`. -/
theorem decodePtrProvenanceM_eq_some_iff {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (p : Gen.Memory.Provenance M) :
    ∀ (bs : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (idx : Nat)
      (acc : Option (Gen.Memory.Provenance M)),
      Interp.decodePtrProvenanceM (M := M) idx acc bs = some p ↔ acc = some p ∧ MrCoh p idx bs
  | [], idx, acc => by
      show acc = some p ↔ acc = some p ∧ True
      exact Iff.intro (fun h => ⟨h, trivial⟩) (fun h => h.1)
  | b :: rest, idx, acc => by
      have ih := decodePtrProvenanceM_eq_some_iff p rest (idx + 1)
      cases b with
      | Uninit =>
          show Interp.decodePtrProvenanceM (M := M) (idx + 1) none rest = some p ↔ _
          rw [ih]
          constructor
          · rintro ⟨h, _⟩
            cases h
          · rintro ⟨_, ⟨v, hv⟩, _⟩
            cases hv
      | Init v frag =>
          cases frag with
          | none =>
              show Interp.decodePtrProvenanceM (M := M) (idx + 1) none rest = some p ↔ _
              rw [ih]
              constructor
              · rintro ⟨h, _⟩
                cases h
              · rintro ⟨_, ⟨v', hv⟩, _⟩
                injection hv with _ h2
                cases h2
          | some f =>
              obtain ⟨fp, fpos⟩ := f
              show Interp.decodePtrProvenanceM (M := M) (idx + 1)
                  (if fpos = (idx : Int) ∧ some fp = acc then acc else none) rest = some p ↔ _
              rw [ih]
              by_cases hc : fpos = (idx : Int) ∧ some fp = acc
              · rw [ite_of_pos hc]
                obtain ⟨h1, h2⟩ := hc
                subst h1
                subst h2
                constructor
                · rintro ⟨h, hr⟩
                  injection h with h
                  subst h
                  exact ⟨rfl, ⟨v, rfl⟩, hr⟩
                · rintro ⟨h, _, hr⟩
                  exact ⟨h, hr⟩
              · rw [ite_of_neg hc]
                constructor
                · rintro ⟨h, _⟩
                  cases h
                · rintro ⟨hacc, ⟨v', hv⟩, _⟩
                  injection hv with _ hfrag
                  injection hfrag with hfrag
                  injection hfrag with hp hpos
                  exact absurd ⟨hpos, by rw [hacc, hp]⟩ hc

/-- The provenance that `decode_ptr` (`decodePtrM`) computes for `bs`. -/
def mrProvM (M : Type) [Gen.Memory M] [Interp.MemoryOps M]
    (bs : List (Gen.AbstractByte (Gen.Memory.Provenance M))) : Option (Gen.Memory.Provenance M) :=
  Interp.decodePtrProvenanceM (M := M) 0 (Interp.firstProvenanceM (M := M) bs) bs

/-- MiniRust retains provenance `p` exactly on non-empty, positionally coherent,
single-provenance byte lists. -/
theorem mrProvM_eq_some_iff {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (bs : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (p : Gen.Memory.Provenance M) :
    mrProvM M bs = some p ↔ bs ≠ [] ∧ MrCoh p 0 bs := by
  unfold mrProvM
  rw [decodePtrProvenanceM_eq_some_iff]
  cases bs with
  | nil =>
      constructor
      · rintro ⟨h, _⟩
        cases h
      · rintro ⟨h, _⟩
        exact absurd rfl h
  | cons b rest =>
      constructor
      · rintro ⟨_, h⟩
        exact ⟨List.cons_ne_nil _ _, h⟩
      · rintro ⟨_, h⟩
        have h1 := h.1
        obtain ⟨v, hv⟩ := h1
        subst hv
        exact ⟨rfl, h⟩

theorem mrProvM_eq_some_of_get {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (bs : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (p : Gen.Memory.Provenance M)
    (hne : bs ≠ [])
    (h : ∀ (i : Nat) (b : Gen.AbstractByte (Gen.Memory.Provenance M)), bs[i]? = some b →
      ∃ v, b = Gen.AbstractByte.Init v (some ⟨p, (i : Int)⟩)) :
    mrProvM M bs = some p := by
  refine (mrProvM_eq_some_iff bs p).mpr ⟨hne, (mrCoh_iff_get p bs 0).mpr ?_⟩
  intro i b hb
  have := h i b hb
  rw [Nat.zero_add]
  exact this

/-- MiniRust strips provenance as soon as one byte is not the fragment of its
own position (wrong position, no fragment, or uninitialized). -/
theorem mrProvM_eq_none_of_bad {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (bs : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (i : Nat)
    (b : Gen.AbstractByte (Gen.Memory.Provenance M)) (hb : bs[i]? = some b)
    (hbad : ∀ v (fr : Gen.ProvenanceFrag (Gen.Memory.Provenance M)),
      b = .Init v (some fr) → fr.position ≠ (i : Int)) :
    mrProvM M bs = none := by
  cases h : mrProvM M bs with
  | none => rfl
  | some p =>
      obtain ⟨_, hc⟩ := (mrProvM_eq_some_iff bs p).mp h
      obtain ⟨v, hv⟩ := (mrCoh_iff_get p bs 0).mp hc i b hb
      have := hbad v _ hv
      rw [Nat.zero_add] at this
      exact absurd rfl this

/-- MiniRust strips provenance when two bytes carry different provenances. -/
theorem mrProvM_eq_none_of_prov_mismatch {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (bs : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (i j : Nat) (vi vj : UInt8)
    (fi fj : Gen.ProvenanceFrag (Gen.Memory.Provenance M))
    (hi : bs[i]? = some (.Init vi (some fi))) (hj : bs[j]? = some (.Init vj (some fj)))
    (hne : fi.provenance ≠ fj.provenance) :
    mrProvM M bs = none := by
  cases h : mrProvM M bs with
  | none => rfl
  | some p =>
      obtain ⟨_, hc⟩ := (mrProvM_eq_some_iff bs p).mp h
      obtain ⟨v1, h1⟩ := (mrCoh_iff_get p bs 0).mp hc i _ hi
      obtain ⟨v2, h2⟩ := (mrCoh_iff_get p bs 0).mp hc j _ hj
      injection h1 with _ h1
      injection h1 with h1
      injection h2 with _ h2
      injection h2 with h2
      subst h1
      subst h2
      exact absurd rfl hne

/-- `decode_ptr` (`decodePtrM`) on 8 bytes: the address is the little-endian
value of the byte data and the provenance is `mrProvM`; any uninitialized byte
makes the decode fail (`none`). -/
theorem decodePtrM_eq {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (bs : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (hlen : bs.length = 8) :
    Interp.decodePtrM (M := M) bs =
      .ok ((bs.mapM Interp.AbstractByte.dataM).map (fun data =>
        { addr := ((Interp.leValue data : Nat) : Int), provenance := mrProvM M bs })) := by
  unfold Interp.decodePtrM
  have hne : ¬ (bs.length ≠ Interp.x86_64.PTR_SIZE.bytes) := by
    rw [hlen]
    exact fun h => h rfl
  rw [ite_of_neg hne]
  cases bs.mapM Interp.AbstractByte.dataM <;> rfl

/-! ### `BasicMemory`-specialized definitions agree with the polymorphic ones -/

theorem data_eq_M :
    Interp.AbstractByte.data = Interp.AbstractByte.dataM (Provenance := Interp.Prov) := by
  funext b
  cases b <;> rfl

theorem decodePtrProvenance_eq_M :
    ∀ (bs : List Interp.Byte) (idx : Nat) (acc : Option Interp.Prov),
      Interp.decodePtrProvenance idx acc bs =
        Interp.decodePtrProvenanceM (M := Interp.BM) idx acc bs
  | [], _, _ => rfl
  | b :: rest, idx, acc => by
      have ih := decodePtrProvenance_eq_M rest (idx + 1)
      cases b with
      | Uninit => exact ih none
      | Init v frag =>
          cases frag with
          | none => exact ih none
          | some f => exact ih _

theorem firstProvenance_eq_M (bs : List Interp.Byte) :
    Interp.firstProvenance bs = Interp.firstProvenanceM (M := Interp.BM) bs := by
  cases bs with
  | nil => rfl
  | cons b rest => cases b <;> rfl

theorem decodePtr_eq_M (bs : List Interp.Byte) :
    Interp.decodePtr bs = Interp.decodePtrM (M := Interp.BM) bs := by
  unfold Interp.decodePtr Interp.decodePtrM
  rw [data_eq_M, firstProvenance_eq_M, decodePtrProvenance_eq_M]
  rfl

theorem encodePtrBytes_eq_M (prov : Option Interp.Prov) :
    ∀ (data : List UInt8) (idx : Nat),
      Interp.encodePtrBytes prov idx data = Interp.encodePtrBytesM (M := Interp.BM) prov idx data
  | [], _ => rfl
  | b :: rest, idx => by
      show Gen.AbstractByte.Init b _ :: Interp.encodePtrBytes prov (idx + 1) rest =
        Gen.AbstractByte.Init b _ :: Interp.encodePtrBytesM (M := Interp.BM) prov (idx + 1) rest
      rw [encodePtrBytes_eq_M prov rest (idx + 1)]
      rfl

theorem encodePtr_eq_M (ptr : Interp.Ptr) :
    Interp.encodePtr ptr = Interp.encodePtrM (M := Interp.BM) ptr := by
  unfold Interp.encodePtr Interp.encodePtrM
  cases Interp.Endianness.encode Interp.x86_64.ENDIANNESS LibSpecr.Signedness.Unsigned
      Interp.x86_64.PTR_SIZE ptr.addr with
  | none => rfl
  | some data => exact congrArg Except.ok (encodePtrBytes_eq_M ptr.provenance data 0)

/-- `encode_ptr` (`encodePtrM`) in terms of the encoded address bytes. The
hypothesis is kept syntactic so that no proof ever reduces
`Endianness.encode` on a symbolic address. -/
theorem encodePtrM_of_encode {M : Type} [Gen.Memory M]
    (ptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (data : List UInt8)
    (h : Interp.Endianness.encode Interp.x86_64.ENDIANNESS LibSpecr.Signedness.Unsigned
      Interp.x86_64.PTR_SIZE ptr.addr = some data) :
    Interp.encodePtrM (M := M) ptr =
      .ok (Interp.encodePtrBytesM (M := M) ptr.provenance 0 data) := by
  unfold Interp.encodePtrM
  rw [h]
  rfl

/-- `encode_ptr` (`BasicMemory`-specialized `encodePtr`) in terms of the encoded address bytes. -/
theorem encodePtr_of_encode (ptr : Interp.Ptr) (data : List UInt8)
    (h : Interp.Endianness.encode Interp.x86_64.ENDIANNESS LibSpecr.Signedness.Unsigned
      Interp.x86_64.PTR_SIZE ptr.addr = some data) :
    Interp.encodePtr ptr = .ok (Interp.encodePtrBytes ptr.provenance 0 data) := by
  unfold Interp.encodePtr
  rw [h]
  rfl

/-- `Endianness::encode(Unsigned, PTR_SIZE, addr)` succeeds on every 64-bit
address and yields its little-endian bytes. -/
theorem endianness_encode_ptr (addr : Nat) (h : addr < 2 ^ 64) :
    Interp.Endianness.encode Interp.x86_64.ENDIANNESS LibSpecr.Signedness.Unsigned
      Interp.x86_64.PTR_SIZE (addr : Int) = some (Interp.leBytes addr 8) := by
  have hb : (2 : Int) ^ Interp.Size.bits Interp.x86_64.PTR_SIZE = 18446744073709551616 := by
    decide
  have h1 : Interp.inBounds (addr : Int) LibSpecr.Signedness.Unsigned Interp.x86_64.PTR_SIZE = true := by
    simp only [Interp.inBounds, hb, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have h2 : ((addr : Int) % (2 : Int) ^ Interp.Size.bits Interp.x86_64.PTR_SIZE).toNat = addr := by
    rw [hb]
    omega
  unfold Interp.Endianness.encode
  rw [ite_of_pos h1, h2]
  rfl

theorem encodePtrBytesM_none_eq_map {M : Type} [Gen.Memory M] :
    ∀ (data : List UInt8) (idx : Nat),
      Interp.encodePtrBytesM (M := M) none idx data = data.map (fun b => .Init b none)
  | [], _ => rfl
  | b :: rest, idx => by
      show Gen.AbstractByte.Init b none :: Interp.encodePtrBytesM (M := M) none (idx + 1) rest =
        Gen.AbstractByte.Init b none :: rest.map (fun b => .Init b none)
      rw [encodePtrBytesM_none_eq_map rest (idx + 1)]

/-- `Type.encodeIntM usize` in terms of the encoded bytes (syntactic hypothesis so no proof
unfolds `Endianness.encode` on a symbolic integer). -/
theorem encodeIntM_usize_of_encode {M : Type} [Gen.Memory M] (n : Int) (data : List UInt8)
    (h : Interp.Endianness.encode Interp.x86_64.ENDIANNESS LibSpecr.Signedness.Unsigned
      Interp.x86_64.PTR_SIZE n = some data) :
    Interp.Type.encodeIntM (M := M) Interp.IntType.usize_ty (.Int n) =
      .ok (data.map (fun b => .Init b none)) := by
  have hty : Interp.IntType.usize_ty = ⟨LibSpecr.Signedness.Unsigned, Interp.x86_64.PTR_SIZE⟩ := rfl
  rw [hty]
  unfold Interp.Type.encodeIntM
  dsimp only
  rw [h]
  rfl

/-- `Type.encodeIntM usize` on any valid 64-bit unsigned integer produces its plain
little-endian bytes. -/
theorem encodeIntM_usize (n : Nat) (h : n < 2 ^ 64) {M : Type} [Gen.Memory M] :
    Interp.Type.encodeIntM (M := M) Interp.IntType.usize_ty (.Int (n : Int)) =
      .ok ((Interp.leBytes n 8).map (fun b => .Init b none)) :=
  encodeIntM_usize_of_encode (n : Int) (Interp.leBytes n 8) (endianness_encode_ptr n h)

/-- Exact characterization of `Interp.encodeWidePtrM` for `.ElementCount` (slice / `str`). -/
theorem encodeWidePtrM_slice_of_encode {M : Type} [Gen.Memory M]
    (addr len : Int) (prov : Option (Gen.Memory.Provenance M)) (d₁ d₂ : List UInt8)
    (h₁ : Interp.Endianness.encode Interp.x86_64.ENDIANNESS LibSpecr.Signedness.Unsigned
      Interp.x86_64.PTR_SIZE addr = some d₁)
    (h₂ : Interp.Endianness.encode Interp.x86_64.ENDIANNESS LibSpecr.Signedness.Unsigned
      Interp.x86_64.PTR_SIZE len = some d₂) :
    Interp.encodeWidePtrM (M := M) .ElementCount
      { thin_pointer := { addr := addr, provenance := prov },
        metadata := some (.ElementCount len) } =
      .ok (Interp.encodePtrBytesM (M := M) prov 0 d₁ ++
        Interp.encodePtrBytesM (M := M) none 0 d₂) := by
  unfold Interp.encodeWidePtrM Interp.PointerMetaKind.encode_as_valueM
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [encodePtrM_of_encode _ d₁ h₁]
  dsimp only [Except.bind]
  rw [encodeIntM_usize_of_encode len d₂ h₂]
  dsimp only [Except.bind]
  rw [encodePtrBytesM_none_eq_map (M := M) d₂ 0]

/-- Exact characterization of `Interp.encodeWidePtrM` for `.ElementCount` on 64-bit naturals. -/
theorem encodeWidePtrM_slice_eq {M : Type} [Gen.Memory M]
    (addr len : Nat) (prov : Option (Gen.Memory.Provenance M))
    (ha : addr < 2 ^ 64) (hl : len < 2 ^ 64) :
    Interp.encodeWidePtrM (M := M) .ElementCount
      { thin_pointer := { addr := (addr : Int), provenance := prov },
        metadata := some (.ElementCount (len : Int)) } =
      .ok (Interp.encodePtrBytesM (M := M) prov 0 (Interp.leBytes addr 8) ++
        Interp.encodePtrBytesM (M := M) none 0 (Interp.leBytes len 8)) :=
  encodeWidePtrM_slice_of_encode (addr : Int) (len : Int) prov _ _
    (endianness_encode_ptr addr ha) (endianness_encode_ptr len hl)

/-- Exact characterization of `Interp.encodeWidePtrM` for `.VTablePointer` (`&dyn Trait`). -/
theorem encodeWidePtrM_dyn_of_encode {M : Type} [Gen.Memory M] (tr : Gen.TraitName)
    (addr vtAddr : Int) (prov vtProv : Option (Gen.Memory.Provenance M)) (d₁ d₂ : List UInt8)
    (h₁ : Interp.Endianness.encode Interp.x86_64.ENDIANNESS LibSpecr.Signedness.Unsigned
      Interp.x86_64.PTR_SIZE addr = some d₁)
    (h₂ : Interp.Endianness.encode Interp.x86_64.ENDIANNESS LibSpecr.Signedness.Unsigned
      Interp.x86_64.PTR_SIZE vtAddr = some d₂) :
    Interp.encodeWidePtrM (M := M) (.VTablePointer tr)
      { thin_pointer := { addr := addr, provenance := prov },
        metadata := some (.VTablePointer { addr := vtAddr, provenance := vtProv }) } =
      .ok (Interp.encodePtrBytesM (M := M) prov 0 d₁ ++
        Interp.encodePtrBytesM (M := M) vtProv 0 d₂) := by
  unfold Interp.encodeWidePtrM Interp.PointerMetaKind.encode_as_valueM
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [encodePtrM_of_encode _ d₁ h₁]
  dsimp only [Except.bind]
  rw [encodePtrM_of_encode _ d₂ h₂]

/-- Exact characterization of `Interp.encodeWidePtrM` for `.VTablePointer` on 64-bit naturals. -/
theorem encodeWidePtrM_dyn_eq {M : Type} [Gen.Memory M] (tr : Gen.TraitName)
    (addr vtAddr : Nat) (prov vtProv : Option (Gen.Memory.Provenance M))
    (ha : addr < 2 ^ 64) (hv : vtAddr < 2 ^ 64) :
    Interp.encodeWidePtrM (M := M) (.VTablePointer tr)
      { thin_pointer := { addr := (addr : Int), provenance := prov },
        metadata := some (.VTablePointer { addr := (vtAddr : Int), provenance := vtProv }) } =
      .ok (Interp.encodePtrBytesM (M := M) prov 0 (Interp.leBytes addr 8) ++
        Interp.encodePtrBytesM (M := M) vtProv 0 (Interp.leBytes vtAddr 8)) :=
  encodeWidePtrM_dyn_of_encode tr (addr : Int) (vtAddr : Int) prov vtProv _ _
    (endianness_encode_ptr addr ha) (endianness_encode_ptr vtAddr hv)

/-- Exact characterization of `Interp.decodeWidePtrM` for `.ElementCount` on 8+8 bytes. -/
theorem decodeWidePtrM_slice_eq {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (d m : List (Gen.AbstractByte (Gen.Memory.Provenance M)))
    (hd : d.length = 8) (hm : m.length = 8) :
    Interp.decodeWidePtrM (M := M) .ElementCount (d ++ m) =
      .ok (match d.mapM Interp.AbstractByte.dataM, m.mapM Interp.AbstractByte.dataM with
        | some dd, some md =>
          some (.Ptr {
            thin_pointer := { addr := ((Interp.leValue dd : Nat) : Int), provenance := mrProvM M d },
            metadata := some (.ElementCount ((Interp.leValue md : Nat) : Int)) })
        | _, _ => none) := by
  have hlen : (d ++ m).length = 2 * Interp.x86_64.PTR_SIZE.bytes := by
    rw [List.length_append, hd, hm]; rfl
  have htake : (d ++ m).take Interp.x86_64.PTR_SIZE.bytes = d := by
    have : Interp.x86_64.PTR_SIZE.bytes = d.length := hd.symm
    rw [this, List.take_left]
  have hdrop : (d ++ m).drop Interp.x86_64.PTR_SIZE.bytes = m := by
    have : Interp.x86_64.PTR_SIZE.bytes = d.length := hd.symm
    rw [this, List.drop_left]
  unfold Interp.decodeWidePtrM
  rw [ite_of_neg (fun h => h hlen), htake, hdrop]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [decodePtrM_eq d hd]
  cases hdm : d.mapM Interp.AbstractByte.dataM with
  | none => rfl
  | some dd =>
    simp only [Option.map_some]
    unfold Interp.decodeMetaFieldM Interp.Type.decodeIntM Interp.IntType.usize_ty
    dsimp only
    have hmne : ¬ (m.length ≠ Interp.x86_64.PTR_SIZE.bytes) := by
      rw [hm]; exact fun h => h rfl
    rw [ite_of_neg hmne]
    cases hmm : m.mapM Interp.AbstractByte.dataM with
    | none => rfl
    | some md => rfl

/-- Exact characterization of `Interp.decodeWidePtrM` for `.VTablePointer` on 8+8 bytes. -/
theorem decodeWidePtrM_dyn_eq {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (tr : Gen.TraitName) (d m : List (Gen.AbstractByte (Gen.Memory.Provenance M)))
    (hd : d.length = 8) (hm : m.length = 8) :
    Interp.decodeWidePtrM (M := M) (.VTablePointer tr) (d ++ m) =
      .ok (match d.mapM Interp.AbstractByte.dataM, m.mapM Interp.AbstractByte.dataM with
        | some dd, some md =>
          some (.Ptr {
            thin_pointer := { addr := ((Interp.leValue dd : Nat) : Int), provenance := mrProvM M d },
            metadata := some (.VTablePointer {
              addr := ((Interp.leValue md : Nat) : Int), provenance := mrProvM M m }) })
        | _, _ => none) := by
  have hlen : (d ++ m).length = 2 * Interp.x86_64.PTR_SIZE.bytes := by
    rw [List.length_append, hd, hm]; rfl
  have htake : (d ++ m).take Interp.x86_64.PTR_SIZE.bytes = d := by
    have : Interp.x86_64.PTR_SIZE.bytes = d.length := hd.symm
    rw [this, List.take_left]
  have hdrop : (d ++ m).drop Interp.x86_64.PTR_SIZE.bytes = m := by
    have : Interp.x86_64.PTR_SIZE.bytes = d.length := hd.symm
    rw [this, List.drop_left]
  unfold Interp.decodeWidePtrM
  rw [ite_of_neg (fun h => h hlen), htake, hdrop]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [decodePtrM_eq d hd]
  cases hdm : d.mapM Interp.AbstractByte.dataM with
  | none => rfl
  | some dd =>
    simp only [Option.map_some]
    unfold Interp.decodeMetaFieldM
    simp only [bind, Except.bind, pure, Except.pure]
    rw [decodePtrM_eq m hm]
    cases hmm : m.mapM Interp.AbstractByte.dataM with
    | none => rfl
    | some md => rfl

/-- Polymorphic MiniRust `Type.decodeM .Bool` exact characterization across `BasicMemory` and
`TreeBorrowsMemory`: accepts `0` (`false`) and `1` (`true`), rejects every other byte (`none`). -/
theorem minirust_bool_decodeM_iff {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (v : UInt8) (fr : Option (Gen.ProvenanceFrag (Gen.Memory.Provenance M))) :
    Interp.Type.decodeM (M := M) .Bool [.Init v fr] =
      (if v = 0 then .ok (some (.Bool false))
       else if v = 1 then .ok (some (.Bool true))
       else .ok none) := by
  by_cases h0 : v = 0
  · subst h0; rfl
  · by_cases h1 : v = 1
    · subst h1; rfl
    · rw [ite_of_neg h0, ite_of_neg h1]
      rw [Interp.Type.decodeM]
      · rfl
      · intro x h; injection h with h _; injection h with hv _; exact h0 hv
      · intro x h; injection h with h _; injection h with hv _; exact h1 hv

/-- Polymorphic MiniRust `Type.decodeM (.Int u8)` accepts every initialized byte (`Kani#5205`). -/
theorem minirust_u8_decodeM {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (v : UInt8) (fr : Option (Gen.ProvenanceFrag (Gen.Memory.Provenance M))) :
    Interp.Type.decodeM (M := M) (.Int ⟨.Unsigned, ⟨1⟩⟩) [.Init v fr] =
      .ok (some (.Int (v.toNat : Int))) := by
  rw [Interp.Type.decodeM]
  rfl

/-- Polymorphic MiniRust `Type.decodeM .Bool` rejects `.Uninit`. -/
theorem minirust_bool_uninit_decodeM {M : Type} [Gen.Memory M] [Interp.MemoryOps M] :
    Interp.Type.decodeM (M := M) .Bool [.Uninit] = .ok none := by
  rw [Interp.Type.decodeM]
  · rfl
  · intro _ h; cases h
  · intro _ h; cases h


/-- The MiniRust little-endian value of `leBytes u n` is `u mod 256 ^ n`. -/
theorem leValue_leBytes : ∀ (n u : Nat), Interp.leValue (Interp.leBytes u n) = u % 256 ^ n
  | 0, u => by
      show 0 = u % 256 ^ 0
      rw [Nat.pow_zero, Nat.mod_one]
  | n + 1, u => by
      show (UInt8.ofNat (u % 256)).toNat + 256 * Interp.leValue (Interp.leBytes (u / 256) n) =
        u % 256 ^ (n + 1)
      rw [leValue_leBytes n (u / 256), u8_ofNat_toNat, Nat.mod_mod, Nat.pow_succ,
        Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]

/-- Provenance-free MiniRust bytes carry exactly their data. -/
theorem mapM_data_init : ∀ (l : List UInt8),
    (l.map (fun b => (Gen.AbstractByte.Init b none : Interp.Byte))).mapM Interp.AbstractByte.data =
      some l
  | [] => rfl
  | b :: rest => by
      rw [List.map_cons, List.mapM_cons, mapM_data_init rest]
      rfl

/-- `encode_ptr` bytes without provenance are plain initialized bytes. -/
theorem encodePtrBytesM_none {M : Type} [Gen.Memory M] :
    ∀ (l : List UInt8) (idx : Nat),
      Interp.encodePtrBytesM (M := M) none idx l = l.map (fun b => Gen.AbstractByte.Init b none)
  | [], _ => rfl
  | _ :: rest, idx => congrArg (List.cons _) (encodePtrBytesM_none rest (idx + 1))

theorem leBytes_length : ∀ (n u : Nat), (Interp.leBytes u n).length = n
  | 0, _ => rfl
  | n + 1, u => congrArg (· + 1) (leBytes_length n (u / 256))

/-- **MiniRust `Type::Int(u32)` accepts every 32-bit pattern** (in particular all 2048 UTF-16
surrogates `0xD800 ..= 0xDFFF` and everything above `0x10FFFF`): the closest MiniRust type to
`char` performs no scalar-value check. -/
theorem minirust_u32_accepts_all (c : Nat) (hc : c < 2 ^ 32) :
    Interp.Type.decode (.Int ⟨.Unsigned, ⟨4⟩⟩)
      ((Interp.leBytes c 4).map (fun b => Gen.AbstractByte.Init b none)) = .ok (some (.Int c)) := by
  show Interp.Type.decodeInt ⟨.Unsigned, ⟨4⟩⟩ _ = _
  unfold Interp.Type.decodeInt
  dsimp only
  have hlen : ¬ (((Interp.leBytes c 4).map (fun b => (Gen.AbstractByte.Init b none : Interp.Byte))).length ≠
      (⟨4⟩ : LibSpecr.Size).bytes) := by
    rw [List.length_map, leBytes_length]
    exact fun h => h rfl
  rw [ite_of_neg hlen, mapM_data_init]
  show Except.ok (some (Gen.Value.Int ((Interp.leValue (Interp.leBytes c 4) : Nat) : Int))) = _
  rw [leValue_leBytes, Nat.mod_eq_of_lt (by omega)]

/-- Memory-polymorphic `AbstractByte.dataM` over plain initialized bytes. -/
theorem mapM_dataM_init {M : Type} [Gen.Memory M] : ∀ (l : List UInt8),
    (l.map (fun b => (Gen.AbstractByte.Init b none : Gen.AbstractByte (Gen.Memory.Provenance M)))).mapM
      Interp.AbstractByte.dataM = some l
  | [] => rfl
  | b :: rest => by
      rw [List.map_cons, List.mapM_cons, mapM_dataM_init rest]
      rfl

/-- Memory-polymorphic MiniRust `Type.decodeM (.Int u32)` accepts every 32-bit pattern across both
`BasicMemory` and `TreeBorrowsMemory`. -/
theorem minirust_u32_decodeM {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (c : Nat) (hc : c < 2 ^ 32) :
    Interp.Type.decodeM (M := M) (.Int ⟨.Unsigned, ⟨4⟩⟩)
      ((Interp.leBytes c 4).map (fun b => Gen.AbstractByte.Init b none)) = .ok (some (.Int c)) := by
  rw [Interp.Type.decodeM]
  unfold Interp.Type.decodeIntM
  dsimp only
  have hlen : ¬ (((Interp.leBytes c 4).map (fun b =>
      (Gen.AbstractByte.Init b none : Gen.AbstractByte (Gen.Memory.Provenance M)))).length ≠
      (⟨4⟩ : LibSpecr.Size).bytes) := by
    rw [List.length_map, leBytes_length]
    exact fun h => h rfl
  rw [ite_of_neg hlen, mapM_dataM_init]
  show Except.ok (some (Gen.Value.Int ((Interp.leValue (Interp.leBytes c 4) : Nat) : Int))) = _
  rw [leValue_leBytes, Nat.mod_eq_of_lt (by omega)]

/-- General 2-range `u32` `Type::Enum` + `Discriminator::Branch` type parameterized by symbolic
interval endpoints `[lo1, hi1)` and `[lo2, hi2)` (keeping endpoint numerals opaque to well-founded
equation-lemma kernel reduction). -/
def minirustTwoRangeU32Enum (lo1 hi1 lo2 hi2 : Int) : Gen.«Type» :=
  .Enum
    ⟨[(0, ⟨.Int ⟨.Unsigned, ⟨4⟩⟩, ⟨[]⟩⟩), (1, ⟨.Int ⟨.Unsigned, ⟨4⟩⟩, ⟨[]⟩⟩)]⟩
    ⟨.Unsigned, ⟨4⟩⟩
    (.Branch ⟨0⟩ ⟨.Unsigned, ⟨4⟩⟩ .Invalid
      ⟨[((lo1, hi1), .Known 0), ((lo2, hi2), .Known 1)]⟩)
    ⟨4⟩ ⟨4⟩

/-- **MiniRust `Type::Enum` + `Discriminator::Branch` encoding of Rust `char`.**
MiniRust models Rust `char` (whose validity invariant is `[0, 0xD800) ∪ [0xE000, 0x110000)`) via
a 2-range `Discriminator::Branch` over the 4-byte unsigned word at offset `0` with fallback
`.Invalid`. -/
def minirustCharType : Gen.«Type» :=
  minirustTwoRangeU32Enum 0 0xD800 0xE000 0x110000

/-- Syntactic helper on symbolic endpoints `[lo1, hi1) ∪ [lo2, hi2)` and symbolic 4-byte stream
`bs`: avoids ever reducing large concrete numerals inside well-founded `Type.decodeM` /
`decodeDiscriminantM` kernel checks. -/
theorem minirust_twoRangeU32Enum_decodeM_of_u32 {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (lo1 hi1 lo2 hi2 : Int)
    (bs : List (Gen.AbstractByte (Gen.Memory.Provenance M))) (c : Int)
    (hlen : bs.length = 4)
    (hu32 : Interp.Type.decodeIntM (M := M) ⟨.Unsigned, ⟨4⟩⟩ bs = .ok (some (.Int c))) :
    Interp.Type.decodeM (M := M) (minirustTwoRangeU32Enum lo1 hi1 lo2 hi2) bs =
      if lo1 ≤ c ∧ c < hi1 then .ok (some (.Variant 0 (.Int c)))
      else if lo2 ≤ c ∧ c < hi2 then .ok (some (.Variant 1 (.Int c)))
      else .ok none := by
  have hsub : Interp.subsliceWithLength bs ((0 : Nat) : Int) ((4 : Nat) : Int) = .ok bs := by
    unfold Interp.subsliceWithLength
    have hcond : (0 : Int) ≤ (0 : Nat) ∧ (0 : Int) ≤ (4 : Nat) ∧ ((0 : Nat) : Int) + (4 : Nat) ≤ bs.length := by
      omega
    rw [ite_of_pos hcond]
    change Except.ok ((bs.drop 0).take 4) = Except.ok bs
    rw [List.drop_zero, List.take_of_length_le (by omega)]
  have hdecU32 : Interp.Type.decodeM (M := M) (.Int ⟨.Unsigned, ⟨4⟩⟩) bs = .ok (some (.Int c)) := by
    rw [Interp.Type.decodeM]; exact hu32
  unfold minirustTwoRangeU32Enum
  rw [Interp.Type.decodeM]
  simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [Interp.decodeDiscriminantM]
  simp only [hsub, hu32, bind, Bind.bind, Except.bind]
  rw [Interp.decodeDiscriminantChildrenM]
  by_cases h1 : lo1 ≤ c ∧ c < hi1
  · rw [ite_of_pos h1, ite_of_pos h1]
    rw [Interp.decodeDiscriminantM]
    dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    rw [Interp.Type.decodeVariantM, ite_of_pos rfl, hdecU32]
  · rw [ite_of_neg h1, ite_of_neg h1]
    rw [Interp.decodeDiscriminantChildrenM]
    by_cases h2 : lo2 ≤ c ∧ c < hi2
    · rw [ite_of_pos h2, ite_of_pos h2]
      rw [Interp.decodeDiscriminantM]
      dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
      rw [Interp.Type.decodeVariantM, ite_of_neg (by decide : ¬ ((0 : Int) = 1)),
        Interp.Type.decodeVariantM, ite_of_pos rfl, hdecU32]
    · rw [ite_of_neg h2, ite_of_neg h2]
      rw [Interp.decodeDiscriminantChildrenM, Interp.decodeDiscriminantM]
      rfl

/-- Exact closed form of memory-polymorphic MiniRust `Type.decodeM minirustCharType` on every
32-bit little-endian pattern `c < 2^32` across both `BasicMemory` and `TreeBorrowsMemory`. -/
theorem minirust_char_decodeM_eq {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (c : Nat) (hc : c < 2 ^ 32) :
    Interp.Type.decodeM (M := M) minirustCharType
      ((Interp.leBytes c 4).map (fun b => Gen.AbstractByte.Init b none)) =
      if c < 0xD800 then .ok (some (.Variant 0 (.Int c)))
      else if 0xE000 ≤ c ∧ c ≤ 0x10FFFF then .ok (some (.Variant 1 (.Int c)))
      else .ok none := by
  have h := minirust_twoRangeU32Enum_decodeM_of_u32 (M := M) 0 0xD800 0xE000 0x110000
    ((Interp.leBytes c 4).map (fun b => Gen.AbstractByte.Init b none)) (c : Int)
    (by simp [leBytes_length]) (by
      have hu := minirust_u32_decodeM (M := M) c hc
      rw [Interp.Type.decodeM] at hu
      exact hu)
  change Interp.Type.decodeM (M := M) (minirustTwoRangeU32Enum 0 0xD800 0xE000 0x110000) _ = _
  rw [h]
  by_cases h1 : c < 0xD800
  · have h1' : (0 : Int) ≤ (c : Int) ∧ (c : Int) < 0xD800 := by omega
    simp only [h1, h1', and_self, ↓reduceIte]
  · have h1' : ¬ ((0 : Int) ≤ (c : Int) ∧ (c : Int) < 0xD800) := by omega
    by_cases h2 : 0xE000 ≤ c ∧ c ≤ 0x10FFFF
    · have h2' : (0xE000 : Int) ≤ (c : Int) ∧ (c : Int) < 0x110000 := by omega
      simp only [h1, h1', h2, h2', and_self, ↓reduceIte]
    · have h2' : ¬ ((0xE000 : Int) ≤ (c : Int) ∧ (c : Int) < 0x110000) := by omega
      simp only [h1, h1', h2, h2', ↓reduceIte]

/-- Universal biconditional characterizing MiniRust `minirustCharType` validity across all
`c < 2^32` and both `BasicMemory` and `TreeBorrowsMemory`. -/
theorem minirust_char_decodeM_iff {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (c : Nat) (hc : c < 2 ^ 32) :
    (∃ v, Interp.Type.decodeM (M := M) minirustCharType
        ((Interp.leBytes c 4).map (fun b => Gen.AbstractByte.Init b none)) = .ok (some v)) ↔
      (c < 0xD800 ∨ (0xE000 ≤ c ∧ c ≤ 0x10FFFF)) := by
  rw [minirust_char_decodeM_eq (M := M) c hc]
  by_cases h1 : c < 0xD800
  · simp [h1]
  · by_cases h2 : 0xE000 ≤ c ∧ c ≤ 0x10FFFF
    · simp [h1, h2]
    · simp [h1, h2]

/-- MiniRust `Type.decodeM minirustCharType` rejects any 4-byte stream starting with `.Uninit`. -/
theorem minirust_char_uninit_decodeM {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (b1 b2 b3 : Gen.AbstractByte (Gen.Memory.Provenance M)) :
    Interp.Type.decodeM (M := M) minirustCharType [.Uninit, b1, b2, b3] = .ok none := by
  unfold minirustCharType minirustTwoRangeU32Enum
  rw [Interp.Type.decodeM]
  have hsub : Interp.subsliceWithLength
      ([Gen.AbstractByte.Uninit, b1, b2, b3] : List (Gen.AbstractByte (Gen.Memory.Provenance M)))
      ((0 : Nat) : Int) ((4 : Nat) : Int) =
      .ok [.Uninit, b1, b2, b3] := by
    unfold Interp.subsliceWithLength
    have hcond : (0 : Int) ≤ (0 : Nat) ∧ (0 : Int) ≤ (4 : Nat) ∧
        ((0 : Nat) : Int) + (4 : Nat) ≤ ([Gen.AbstractByte.Uninit, b1, b2, b3] : List (Gen.AbstractByte (Gen.Memory.Provenance M))).length := by
      simp
    rw [ite_of_pos hcond]; rfl
  have hint : Interp.Type.decodeIntM (M := M) ⟨.Unsigned, ⟨4⟩⟩ [.Uninit, b1, b2, b3] = .ok none := by
    unfold Interp.Type.decodeIntM; rfl
  simp only [List.length_cons, List.length_nil, ne_eq, not_true_eq_false, ↓reduceIte,
    bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [Interp.decodeDiscriminantM]
  simp only [hsub, bind, Bind.bind, Except.bind, hint]
  rfl

end Shared

/-! ## `V2026_06_01`: correspondence of `Trusted.Rustc.V2026_06_01.MirSemantics` with `MiniRustSpec.Interp` -/

namespace V06

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ### §1. The fragment projection -/

/-- The exact fragment projection `PtrByteFrag → ProvenanceFrag { provenance, position := byteIdx }`.
It forgets `origOffset` and `ptrBytes`, which MiniRust fragments do not carry. -/
def projFrag {P : Type} (pv : Nat → Nat → P) (f : PtrByteFrag) : Gen.ProvenanceFrag P :=
  { provenance := pv f.allocId f.tag, position := (f.byteIdx : Int) }

/-- Projection of a `Trusted` abstract byte to a MiniRust `AbstractByte`. -/
def projByte {P : Type} (pv : Nat → Nat → P) : AbstractByte → Gen.AbstractByte P
  | .uninit => .Uninit
  | .init b none => .Init b none
  | .init b (some f) => .Init b (some (projFrag pv f))

/-- Projection of a `Trusted` byte stream to a MiniRust byte list. -/
def projBytes {P : Type} (pv : Nat → Nat → P) (bs : List AbstractByte) :
    List (Gen.AbstractByte P) :=
  bs.map (projByte pv)

theorem projBytes_length {P : Type} (pv : Nat → Nat → P) (bs : List AbstractByte) :
    (projBytes pv bs).length = bs.length :=
  List.length_map _

theorem projBytes_get {P : Type} (pv : Nat → Nat → P) (bs : List AbstractByte) (i : Nat)
    (b : AbstractByte) (h : bs[i]? = some b) :
    (projBytes pv bs)[i]? = some (projByte pv b) := by
  unfold projBytes
  rw [List.getElem?_map, h]
  rfl

theorem projByte_eq_init_some {P : Type} (pv : Nat → Nat → P) (b : AbstractByte) (v : UInt8)
    (fr : Gen.ProvenanceFrag P) (h : projByte pv b = .Init v (some fr)) :
    ∃ f, b = .init v (some f) ∧ projFrag pv f = fr := by
  cases b with
  | uninit =>
      have h' : (Gen.AbstractByte.Uninit : Gen.AbstractByte P) = .Init v (some fr) := h
      cases h'
  | init w pr =>
      cases pr with
      | none =>
          have h' : Gen.AbstractByte.Init w (none : Option (Gen.ProvenanceFrag P)) =
              .Init v (some fr) := h
          injection h' with _ h2
          cases h2
      | some f =>
          have h' : Gen.AbstractByte.Init w (some (projFrag pv f)) = .Init v (some fr) := h
          injection h' with h1 h2
          injection h2 with h2
          subst h1
          exact ⟨f, rfl, h2⟩

theorem frag_ext (f g : PtrByteFrag) (h1 : f.allocId = g.allocId) (h2 : f.tag = g.tag)
    (h3 : f.byteIdx = g.byteIdx) (h4 : f.origOffset = g.origOffset)
    (h5 : f.ptrBytes = g.ptrBytes) : f = g := by
  cases f
  cases g
  simp_all

/-! ### §2. Exact characterization of `Trusted` fragment coherence -/

/-- `Trusted` positional coherence: byte `i` of `bs` (the first one having index
`idx`) is `.init _ (some { allocId := a, tag := t, byteIdx := idx + i, origOffset := o,
ptrBytes := pb })`, and the stream ends exactly at index `pb`. -/
def TrCoh (a t o pb : Nat) : Nat → List AbstractByte → Prop
  | idx, [] => idx = pb
  | idx, b :: rest => (∃ v, b = .init v (some ⟨a, t, idx, o, pb⟩)) ∧ TrCoh a t o pb (idx + 1) rest

theorem coherentAux_iff (a t o pb : Nat) :
    ∀ (bs : List AbstractByte) (idx : Nat),
      abstractBytesCoherentPtrProvAux a t o pb idx bs = true ↔ TrCoh a t o pb idx bs
  | [], idx => nat_beq_iff idx pb
  | b :: rest, idx => by
      have ih := coherentAux_iff a t o pb rest (idx + 1)
      cases b with
      | uninit =>
          show false = true ↔ _
          constructor
          · intro h
            cases h
          · rintro ⟨⟨v, hv⟩, _⟩
            cases hv
      | init v frag =>
          cases frag with
          | none =>
              show false = true ↔ _
              constructor
              · intro h
                cases h
              · rintro ⟨⟨v', hv⟩, _⟩
                injection hv with _ h2
                cases h2
          | some f =>
              obtain ⟨fa, ft, fi, fo, fpb⟩ := f
              show (Bool.and (Bool.and (Nat.beq fa a) (Bool.and (Nat.beq ft t)
                    (Bool.and (Nat.beq fi idx) (Bool.and (Nat.beq fo o) (Nat.beq fpb pb)))))
                  (abstractBytesCoherentPtrProvAux a t o pb (idx + 1) rest)) = true ↔
                (∃ v', AbstractByte.init v (some ⟨fa, ft, fi, fo, fpb⟩) =
                    .init v' (some ⟨a, t, idx, o, pb⟩)) ∧ TrCoh a t o pb (idx + 1) rest
              simp only [Bool.and_eq_true, nat_beq_iff, ih]
              constructor
              · rintro ⟨⟨h1, h2, h3, h4, h5⟩, hr⟩
                subst h1 h2 h3 h4 h5
                exact ⟨⟨v, rfl⟩, hr⟩
              · rintro ⟨⟨v', hv⟩, hr⟩
                injection hv with _ e2
                injection e2 with e2
                injection e2 with e1 e2 e3 e4 e5
                exact ⟨⟨e1, e2, e3, e4, e5⟩, hr⟩

/-- The coherence guard of `abstractBytesCoherentPtrProv?` on a fragment-headed stream. -/
def cohCond (g : PtrByteFrag) (rest : List AbstractByte) : Bool :=
  Bool.and (Nat.blt 0 g.ptrBytes)
    (Bool.and (Nat.beq g.byteIdx 0)
      (abstractBytesCoherentPtrProvAux g.allocId g.tag g.origOffset g.ptrBytes 1 rest))

theorem coherent?_cons_iff (v : UInt8) (g f : PtrByteFrag) (rest : List AbstractByte) :
    abstractBytesCoherentPtrProv? (.init v (some g) :: rest) = some f ↔
      cohCond g rest = true ∧ g = f := by
  show (match cohCond g rest with
    | true => some g
    | false => none) = some f ↔ _
  cases cohCond g rest
  · constructor
    · intro h
      cases h
    · rintro ⟨h, _⟩
      cases h
  · constructor
    · intro h
      injection h with h
      exact ⟨rfl, h⟩
    · rintro ⟨_, h⟩
      exact congrArg some h

/-- **Exact characterization of `abstractBytesCoherentPtrProv?`.** -/
theorem coherent?_eq_some_iff (bs : List AbstractByte) (f : PtrByteFrag) :
    abstractBytesCoherentPtrProv? bs = some f ↔
      0 < f.ptrBytes ∧ f.byteIdx = 0 ∧
        TrCoh f.allocId f.tag f.origOffset f.ptrBytes 0 bs := by
  cases bs with
  | nil =>
      show (none : Option PtrByteFrag) = some f ↔ _
      constructor
      · intro h
        cases h
      · rintro ⟨h0, _, h⟩
        have h' : 0 = f.ptrBytes := h
        omega
  | cons b rest =>
      cases b with
      | uninit =>
          show (none : Option PtrByteFrag) = some f ↔ _
          constructor
          · intro h
            cases h
          · rintro ⟨_, _, ⟨v, hv⟩, _⟩
            cases hv
      | init v frag =>
          cases frag with
          | none =>
              show (none : Option PtrByteFrag) = some f ↔ _
              constructor
              · intro h
                cases h
              · rintro ⟨_, _, ⟨v', hv⟩, _⟩
                injection hv with _ h2
                cases h2
          | some g =>
              rw [coherent?_cons_iff]
              unfold cohCond
              simp only [Bool.and_eq_true, nat_beq_iff, Nat.blt_eq, coherentAux_iff]
              constructor
              · rintro ⟨⟨h0, hi, hr⟩, hgf⟩
                subst hgf
                refine ⟨h0, hi, And.intro ⟨v, ?_⟩ hr⟩
                exact congrArg (fun x => AbstractByte.init v (some x))
                  (frag_ext _ _ rfl rfl hi rfl rfl)
              · rintro ⟨h0, hi, ⟨v', hv⟩, hr⟩
                injection hv with _ e2
                injection e2 with e2
                have hgf : g = f := by
                  rw [e2]
                  exact frag_ext _ _ rfl rfl hi.symm rfl rfl
                subst hgf
                exact ⟨⟨h0, hi, hr⟩, rfl⟩

theorem trCoh_get (a t o pb : Nat) :
    ∀ (bs : List AbstractByte) (idx : Nat), TrCoh a t o pb idx bs →
      ∀ (i : Nat) (b : AbstractByte), bs[i]? = some b →
        ∃ v, b = AbstractByte.init v (some ⟨a, t, idx + i, o, pb⟩)
  | [], _, _ => by
      intro i b hb
      cases hb
  | x :: rest, idx, h => by
      intro i b hb
      cases i with
      | zero =>
          have hx : some x = some b := hb
          injection hx with hx
          subst hx
          exact h.1
      | succ j =>
          have hb' : rest[j]? = some b := hb
          have := trCoh_get a t o pb rest (idx + 1) h.2 j b hb'
          have e : idx + 1 + j = idx + (j + 1) := by omega
          rw [e] at this
          exact this

theorem trCoh_of_get (a t o pb : Nat) :
    ∀ (bs : List AbstractByte) (idx : Nat), idx + bs.length = pb →
      (∀ (i : Nat) (b : AbstractByte), bs[i]? = some b →
        ∃ v, b = AbstractByte.init v (some ⟨a, t, idx + i, o, pb⟩)) →
      TrCoh a t o pb idx bs
  | [], idx, hlen, _ => by
      show idx = pb
      simpa using hlen
  | x :: rest, idx, hlen, h => by
      refine And.intro (h 0 x rfl) (trCoh_of_get a t o pb rest (idx + 1) ?_ ?_)
      · simp only [List.length_cons] at hlen
        omega
      · intro j b hb
        have := h (j + 1) b hb
        have e : idx + (j + 1) = idx + 1 + j := by omega
        rw [e] at this
        exact this

theorem trCoh_length (a t o pb : Nat) :
    ∀ (bs : List AbstractByte) (idx : Nat), TrCoh a t o pb idx bs → idx + bs.length = pb
  | [], idx, h => by
      have h' : idx = pb := h
      simpa using h'
  | _ :: rest, idx, h => by
      have := trCoh_length a t o pb rest (idx + 1) h.2
      simp only [List.length_cons]
      omega

/-- `Trusted` strips provenance as soon as one byte is not the fragment of its
own position (wrong `byteIdx`, no fragment, or uninitialized). -/
theorem coherent?_none_of_bad_position (bs : List AbstractByte) (i : Nat) (b : AbstractByte)
    (hb : bs[i]? = some b) (hbad : ∀ v f, b = .init v (some f) → f.byteIdx ≠ i) :
    abstractBytesCoherentPtrProv? bs = none := by
  cases h : abstractBytesCoherentPtrProv? bs with
  | none => rfl
  | some f =>
      obtain ⟨_, _, hc⟩ := (coherent?_eq_some_iff bs f).mp h
      obtain ⟨v, hv⟩ := trCoh_get _ _ _ _ bs 0 hc i b hb
      have := hbad v _ hv
      rw [Nat.zero_add] at this
      exact absurd rfl this

/-- `Trusted` strips provenance when two fragments disagree on the allocation,
the tag, the originating offset, or the pointer width. -/
theorem coherent?_none_of_field_mismatch (bs : List AbstractByte) (i j : Nat) (vi vj : UInt8)
    (fi fj : PtrByteFrag)
    (hi : bs[i]? = some (.init vi (some fi))) (hj : bs[j]? = some (.init vj (some fj)))
    (hne : fi.allocId ≠ fj.allocId ∨ fi.tag ≠ fj.tag ∨ fi.origOffset ≠ fj.origOffset ∨
      fi.ptrBytes ≠ fj.ptrBytes) :
    abstractBytesCoherentPtrProv? bs = none := by
  cases h : abstractBytesCoherentPtrProv? bs with
  | none => rfl
  | some f =>
      obtain ⟨_, _, hc⟩ := (coherent?_eq_some_iff bs f).mp h
      obtain ⟨v1, h1⟩ := trCoh_get _ _ _ _ bs 0 hc i _ hi
      obtain ⟨v2, h2⟩ := trCoh_get _ _ _ _ bs 0 hc j _ hj
      injection h1 with _ h1
      injection h1 with h1
      injection h2 with _ h2
      injection h2 with h2
      subst h1
      subst h2
      rcases hne with h | h | h | h <;> exact absurd rfl h

/-! ### §3. `Trusted → MiniRust` soundness: coherent streams decode identically -/

theorem trCoh_proj {P : Type} (pv : Nat → Nat → P) (a t o pb : Nat) :
    ∀ (bs : List AbstractByte) (idx : Nat), TrCoh a t o pb idx bs →
      MrCoh (pv a t) idx (projBytes pv bs)
  | [], _, _ => trivial
  | x :: rest, idx, h => by
      obtain ⟨⟨v, hv⟩, hr⟩ := h
      subst hv
      exact And.intro ⟨v, rfl⟩ (trCoh_proj pv a t o pb rest (idx + 1) hr)

/-- **Directional refinement (`Trusted` retains ⟹ MiniRust retains).** Whenever
`Trusted` finds the stream coherent, MiniRust `decode_ptr` retains the projected
provenance. -/
theorem trusted_coherent_implies_minirust_retains {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte) (f : PtrByteFrag)
    (h : abstractBytesCoherentPtrProv? bs = some f) :
    mrProvM M (projBytes pv bs) = some (pv f.allocId f.tag) := by
  obtain ⟨h0, _, hc⟩ := (coherent?_eq_some_iff bs f).mp h
  refine (mrProvM_eq_some_iff _ _).mpr ⟨?_, trCoh_proj pv _ _ _ _ bs 0 hc⟩
  cases bs with
  | nil =>
      have h' : 0 = f.ptrBytes := hc
      omega
  | cons b rest => exact List.cons_ne_nil _ _

/-- The directional refinement as an implication between the two verdicts. -/
theorem trusted_retains_implies_minirust_retains {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte)
    (h : (abstractBytesCoherentPtrProv? bs).isSome = true) :
    (mrProvM M (projBytes pv bs)).isSome = true := by
  cases hc : abstractBytesCoherentPtrProv? bs with
  | none =>
      rw [hc] at h
      cases h
  | some f =>
      rw [trusted_coherent_implies_minirust_retains pv bs f hc]
      rfl

/-- The byte data of a `Trusted` stream (`none` if any byte is uninitialized). -/
def trData : List AbstractByte → Option (List UInt8)
  | [] => some []
  | .uninit :: _ => none
  | .init b _ :: rest => (trData rest).map (b :: ·)

theorem proj_data {P : Type} (pv : Nat → Nat → P) :
    ∀ bs : List AbstractByte,
      (projBytes pv bs).mapM Interp.AbstractByte.dataM = trData bs
  | [] => rfl
  | .uninit :: rest => by
      show List.mapM Interp.AbstractByte.dataM (Gen.AbstractByte.Uninit :: projBytes pv rest) = none
      rw [List.mapM_cons]
      rfl
  | .init b none :: rest => by
      show List.mapM Interp.AbstractByte.dataM (Gen.AbstractByte.Init b none :: projBytes pv rest) =
        (trData rest).map (b :: ·)
      rw [List.mapM_cons, proj_data pv rest]
      cases trData rest <;> rfl
  | .init b (some f) :: rest => by
      show List.mapM Interp.AbstractByte.dataM
          (Gen.AbstractByte.Init b (some (projFrag pv f)) :: projBytes pv rest) =
        (trData rest).map (b :: ·)
      rw [List.mapM_cons, proj_data pv rest]
      cases trData rest <;> rfl

theorem bits_eq_leValue :
    ∀ bs : List AbstractByte, decodeLittleEndianBits bs = (trData bs).map Interp.leValue
  | [] => rfl
  | .uninit :: _ => rfl
  | .init b fr :: rest => by
      show (match decodeLittleEndianBits rest with
        | some highBits => some (Nat.add b.toBitVec.toNat (Nat.mul 256 highBits))
        | none => none) = ((trData rest).map (b :: ·)).map Interp.leValue
      rw [bits_eq_leValue rest]
      cases trData rest <;> rfl

theorem trCoh_data (a t o pb : Nat) :
    ∀ (bs : List AbstractByte) (idx : Nat), TrCoh a t o pb idx bs → ∃ data, trData bs = some data
  | [], _, _ => ⟨[], rfl⟩
  | x :: rest, idx, h => by
      obtain ⟨⟨v, hv⟩, hr⟩ := h
      obtain ⟨data, hd⟩ := trCoh_data a t o pb rest (idx + 1) hr
      subst hv
      refine ⟨v :: data, ?_⟩
      show (trData rest).map (v :: ·) = some (v :: data)
      rw [hd]
      rfl

theorem trData_none_of_uninit :
    ∀ bs : List AbstractByte, AbstractByte.uninit ∈ bs → trData bs = none
  | [], h => by cases h
  | .uninit :: _, _ => rfl
  | .init b fr :: rest, h => by
      have hr : AbstractByte.uninit ∈ rest := by
        cases h with
        | tail _ h' => exact h'
      show (trData rest).map (b :: ·) = none
      rw [trData_none_of_uninit rest hr]
      rfl

/-- MiniRust `decode_ptr` on the projection of an 8-byte `Trusted` stream. -/
theorem decodePtrM_proj {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte) (hlen : bs.length = 8) :
    Interp.decodePtrM (M := M) (projBytes pv bs) =
      .ok ((trData bs).map (fun data =>
        { addr := ((Interp.leValue data : Nat) : Int),
          provenance := mrProvM M (projBytes pv bs) })) := by
  rw [decodePtrM_eq _ (by rw [projBytes_length]; exact hlen), proj_data]

/-! ### §4. The `Trusted` thin-pointer decoder -/

/-- The thin-pointer half of `decodePtrBytesNoForge` (its local `dataOf`). -/
def thinDecode (isRef : Bool) (ptrBytes : Nat) (dataBytes : List AbstractByte) : Option Value :=
  match Nat.blt 0 ptrBytes, Nat.beq (length dataBytes) ptrBytes,
      decodeLittleEndianBits dataBytes with
  | true, true, .some bits =>
    match abstractBytesCoherentPtrProv? dataBytes with
    | .some frag =>
      match Nat.beq frag.ptrBytes ptrBytes with
      | true => .some (.ptr { allocId := frag.allocId, offsetBytes := bits } ptrBytes)
      | false =>
        match isRef with
        | true => .none
        | false => .some (.scalar ⟨bits, ptrBytes⟩)
    | .none =>
      match isRef with
      | true => .none
      | false => .some (.scalar ⟨bits, ptrBytes⟩)
  | _, _, _ => .none

/-- Pointees of thin pointers (everything but slices, `str`, and trait objects). -/
def thinPointee : RigidTy → Bool
  | .slice _ => false
  | .str => false
  | .dynamic _ => false
  | _ => true

/-- On a thin pointee, `decodePtrBytesNoForge` is `thinDecode`. -/
theorem decodePtrBytesNoForge_thin (isRef : Bool) (pointee : RigidTy) (pb : Nat)
    (bs : List AbstractByte) (h : thinPointee pointee = true) :
    decodePtrBytesNoForge isRef pointee pb bs = thinDecode isRef pb bs := by
  cases pointee <;> first | rfl | cases h

theorem thinDecode_coherent (isRef : Bool) (pb : Nat) (bs : List AbstractByte) (bits : Nat)
    (f : PtrByteFrag) (h0 : 0 < pb) (hlen : bs.length = pb)
    (hbits : decodeLittleEndianBits bs = some bits)
    (h : abstractBytesCoherentPtrProv? bs = some f) (hw : f.ptrBytes = pb) :
    thinDecode isRef pb bs = some (.ptr { allocId := f.allocId, offsetBytes := bits } pb) := by
  have e1 : Nat.blt 0 pb = true := by
    rw [Nat.blt_eq]
    exact h0
  have e2 : Nat.beq (length bs) pb = true := (nat_beq_iff _ _).mpr hlen
  have e3 : Nat.beq f.ptrBytes pb = true := (nat_beq_iff _ _).mpr hw
  unfold thinDecode
  rw [e1, e2, hbits]
  simp only [h, e3]

/-- A raw pointer read from an incoherent stream is an integer: no provenance is forged. -/
theorem thinDecode_raw_incoherent (pb : Nat) (bs : List AbstractByte) (bits : Nat)
    (h0 : 0 < pb) (hlen : bs.length = pb) (hbits : decodeLittleEndianBits bs = some bits)
    (h : abstractBytesCoherentPtrProv? bs = none) :
    thinDecode false pb bs = some (.scalar ⟨bits, pb⟩) := by
  have e1 : Nat.blt 0 pb = true := by
    rw [Nat.blt_eq]
    exact h0
  have e2 : Nat.beq (length bs) pb = true := (nat_beq_iff _ _).mpr hlen
  unfold thinDecode
  rw [e1, e2, hbits]
  simp only [h]

/-- A reference / `fn` pointer read from an incoherent stream is invalid. -/
theorem thinDecode_ref_incoherent (pb : Nat) (bs : List AbstractByte)
    (h : abstractBytesCoherentPtrProv? bs = none) :
    thinDecode true pb bs = none := by
  unfold thinDecode
  cases Nat.blt 0 pb <;> cases Nat.beq (length bs) pb <;>
    cases decodeLittleEndianBits bs <;> simp only [h]

/-- Any uninitialized byte makes the pointer decode fail. -/
theorem thinDecode_uninit (isRef : Bool) (pb : Nat) (bs : List AbstractByte)
    (h : decodeLittleEndianBits bs = none) : thinDecode isRef pb bs = none := by
  unfold thinDecode
  rw [h]
  cases Nat.blt 0 pb <;> cases Nat.beq (length bs) pb <;> rfl

/-- **`Trusted → MiniRust` soundness (`UCG#558` W1).** Whenever a `Trusted`
8-byte stream is coherent with `ptrBytes = 8`, both authorities decode it to the
same address with the same (projected) provenance: `Trusted` to a `Value.ptr`
(for raw pointers and references alike) and MiniRust to a `ThinPointer` with
`some` provenance. -/
theorem coherent_decode_agreement {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte) (f : PtrByteFrag)
    (isRef : Bool) (hlen : bs.length = 8)
    (h : abstractBytesCoherentPtrProv? bs = some f) (hw : f.ptrBytes = 8) :
    ∃ data, trData bs = some data ∧
      thinDecode isRef 8 bs =
        some (.ptr { allocId := f.allocId, offsetBytes := Interp.leValue data } 8) ∧
      Interp.decodePtrM (M := M) (projBytes pv bs) =
        .ok (some { addr := ((Interp.leValue data : Nat) : Int),
                    provenance := some (pv f.allocId f.tag) }) := by
  obtain ⟨_, _, hc⟩ := (coherent?_eq_some_iff bs f).mp h
  obtain ⟨data, hd⟩ := trCoh_data _ _ _ _ bs 0 hc
  have hbits : decodeLittleEndianBits bs = some (Interp.leValue data) := by
    rw [bits_eq_leValue, hd]
    rfl
  refine ⟨data, hd, thinDecode_coherent isRef 8 bs _ f (by decide) hlen hbits h hw, ?_⟩
  rw [decodePtrM_proj pv bs hlen, hd, trusted_coherent_implies_minirust_retains pv bs f h]
  rfl

/-- `decodeScalarLayoutBytesNoForge` at a pointer scalar layout on a coherent stream. -/
theorem scalarLayoutPtr_coherent (addrSpace : Nat)
    (vr : Trusted.Rustc.V2026_06_01.Layout.WrappingRange) (bs : List AbstractByte) (bits : Nat)
    (f : PtrByteFrag) (policy : Ptr2IntTransmutePolicy) (hlen : bs.length = 8)
    (hbits : decodeLittleEndianBits bs = some bits)
    (h : abstractBytesCoherentPtrProv? bs = some f) (hw : f.ptrBytes = 8) :
    decodeScalarLayoutBytesNoForge (.initialized (.pointer addrSpace) vr) bs policy 8 =
      some (.ptr { allocId := f.allocId, offsetBytes := bits } 8) := by
  have e2 : Nat.beq (length bs) 8 = true := (nat_beq_iff _ _).mpr hlen
  have e3 : Nat.beq f.ptrBytes 8 = true := (nat_beq_iff _ _).mpr hw
  unfold decodeScalarLayoutBytesNoForge
  simp only [e2, hbits, h, e3]

/-- `decodeScalarLayoutBytesNoForge` at a pointer scalar layout on an incoherent
stream never forges provenance: the result is an integer scalar or invalid. -/
theorem scalarLayoutPtr_incoherent (addrSpace : Nat)
    (vr : Trusted.Rustc.V2026_06_01.Layout.WrappingRange) (bs : List AbstractByte) (bits : Nat)
    (policy : Ptr2IntTransmutePolicy) (hlen : bs.length = 8)
    (hbits : decodeLittleEndianBits bs = some bits)
    (h : abstractBytesCoherentPtrProv? bs = none) :
    decodeScalarLayoutBytesNoForge (.initialized (.pointer addrSpace) vr) bs policy 8 =
      (match wrappingRangeContains vr bits with
       | true => some (.scalar ⟨bits, 8⟩)
       | false => none) := by
  have e2 : Nat.beq (length bs) 8 = true := (nat_beq_iff _ _).mpr hlen
  unfold decodeScalarLayoutBytesNoForge
  simp only [e2, hbits, h]
  cases wrappingRangeContains vr bits <;> rfl

/-- `decodeScalarLayoutBytesNoForge` at a union pointer scalar layout on a coherent stream, for
any positive pointer width `pb` (including 32-bit `4` and 64-bit `8`). -/
theorem scalarLayoutPtr_union_coherent (addrSpace pb : Nat) (bs : List AbstractByte) (bits : Nat)
    (f : PtrByteFrag) (policy : Ptr2IntTransmutePolicy) (h0 : 0 < pb) (hlen : bs.length = pb)
    (hbits : decodeLittleEndianBits bs = some bits)
    (h : abstractBytesCoherentPtrProv? bs = some f) (hw : f.ptrBytes = pb) :
    decodeScalarLayoutBytesNoForge (.union (.pointer addrSpace)) bs policy pb =
      some (.ptr { allocId := f.allocId, offsetBytes := bits } pb) := by
  have hne : Nat.beq pb 0 = false := by cases pb with | zero => omega | succ _ => rfl
  have e2 : Nat.beq (length bs) pb = true := (nat_beq_iff _ _).mpr hlen
  have e3 : Nat.beq f.ptrBytes pb = true := (nat_beq_iff _ _).mpr hw
  unfold decodeScalarLayoutBytesNoForge scalarLayoutByteWidth primitiveKindByteWidth
  simp only [hne, e2, hbits, h, e3]

/-- `decodeScalarLayoutBytesNoForge` at a union pointer scalar layout on an incoherent stream never
forges provenance, for any positive pointer width `pb` (32-bit `4` or 64-bit `8`). -/
theorem scalarLayoutPtr_union_incoherent (addrSpace pb : Nat) (bs : List AbstractByte) (bits : Nat)
    (policy : Ptr2IntTransmutePolicy) (h0 : 0 < pb) (hlen : bs.length = pb)
    (hbits : decodeLittleEndianBits bs = some bits)
    (h : abstractBytesCoherentPtrProv? bs = none) :
    decodeScalarLayoutBytesNoForge (.union (.pointer addrSpace)) bs policy pb =
      some (.scalar ⟨bits, pb⟩) := by
  have hne : Nat.beq pb 0 = false := by cases pb with | zero => omega | succ _ => rfl
  have e2 : Nat.beq (length bs) pb = true := (nat_beq_iff _ _).mpr hlen
  unfold decodeScalarLayoutBytesNoForge scalarLayoutByteWidth primitiveKindByteWidth
  simp only [hne, e2, hbits, h]

/-- **UCG#630 W5 law**: `decodeScalarLayoutBytesNoForge` under `.strictUcg630Ub` rejects any
provenance-bearing byte stream at non-pointer integer scalar layouts (both `.initialized` and
`.union`). -/
theorem scalarLayoutNonPtr_strictUb_rejects_prov (bitWidth : Nat) (signed : Bool)
    (vr : Trusted.Rustc.V2026_06_01.Layout.WrappingRange) (pb : Nat) (bs : List AbstractByte)
    (hp : abstractBytesHaveProv bs = true) :
    decodeScalarLayoutBytesNoForge (.initialized (.int bitWidth signed) vr) bs .strictUcg630Ub pb = none ∧
    decodeScalarLayoutBytesNoForge (.union (.int bitWidth signed)) bs .strictUcg630Ub pb = none := by
  constructor <;> (
    unfold decodeScalarLayoutBytesNoForge
    cases scalarLayoutByteWidth _ pb with
    | none => rfl
    | some sz =>
      dsimp only
      cases Nat.beq (length bs) sz <;> simp [hp])

/-! ### §5. Exact encoding and intact round trips -/

theorem proj_encodeAux {M : Type} [Gen.Memory M] (pv : Nat → Nat → Gen.Memory.Provenance M)
    (a t o pb : Nat) :
    ∀ (n bits idx : Nat),
      projBytes pv (encodePtrBytesAux a t o pb bits idx n) =
        Interp.encodePtrBytesM (M := M) (some (pv a t)) idx (Interp.leBytes bits n)
  | 0, _, _ => rfl
  | n + 1, bits, idx => by
      have ih := proj_encodeAux pv a t o pb n (bits / 256) (idx + 1)
      show Gen.AbstractByte.Init (UInt8.ofNat bits) (some (projFrag pv ⟨a, t, idx, o, pb⟩)) ::
          projBytes pv (encodePtrBytesAux a t o pb (bits / 256) (idx + 1) n) =
        Gen.AbstractByte.Init (UInt8.ofNat (bits % 256)) (some ⟨pv a t, (idx : Int)⟩) ::
          Interp.encodePtrBytesM (M := M) (some (pv a t)) (idx + 1) (Interp.leBytes (bits / 256) n)
      rw [u8_ofNat_mod, ih]
      rfl

/-- **Exact pointer byte encoding.** The projection of the `Trusted` encoding of
a provenance-carrying pointer is exactly the MiniRust `encode_ptr` byte list of
the same address and the projected provenance. -/
theorem proj_encodePtrBytes {M : Type} [Gen.Memory M] (pv : Nat → Nat → Gen.Memory.Provenance M)
    (bits pb a t : Nat) :
    projBytes pv (encodePtrBytes bits pb a t) =
      Interp.encodePtrBytesM (M := M) (some (pv a t)) 0 (Interp.leBytes bits pb) :=
  proj_encodeAux pv a t _ pb pb bits 0

/-- A provenance-free pointer (`encodePlainLittleEndianBytes`) projects to the
MiniRust encoding of a pointer without provenance. -/
theorem proj_plain_bytes {M : Type} [Gen.Memory M] (pv : Nat → Nat → Gen.Memory.Provenance M) :
    ∀ (n bits idx : Nat),
      projBytes pv (encodePlainLittleEndianBytes bits n) =
        Interp.encodePtrBytesM (M := M) none idx (Interp.leBytes bits n)
  | 0, _, _ => rfl
  | n + 1, bits, idx => by
      have ih := proj_plain_bytes pv n (bits / 256) (idx + 1)
      show Gen.AbstractByte.Init (UInt8.ofNat bits) none ::
          projBytes pv (encodePlainLittleEndianBytes (bits / 256) n) =
        Gen.AbstractByte.Init (UInt8.ofNat (bits % 256)) none ::
          Interp.encodePtrBytesM (M := M) none (idx + 1) (Interp.leBytes (bits / 256) n)
      rw [u8_ofNat_mod, ih]

/-- **MiniRust `encode_ptr` agrees with `Trusted` on every valid 64-bit pointer.** -/
theorem encodePtrM_proj {M : Type} [Gen.Memory M] (pv : Nat → Nat → Gen.Memory.Provenance M)
    (addr a t : Nat) (h : addr < 2 ^ 64) :
    Interp.encodePtrM (M := M) { addr := (addr : Int), provenance := some (pv a t) } =
      .ok (projBytes pv (encodePtrBytes addr 8 a t)) :=
  (encodePtrM_of_encode (M := M) { addr := (addr : Int), provenance := some (pv a t) }
      (Interp.leBytes addr 8) (endianness_encode_ptr addr h)).trans
    (congrArg Except.ok (proj_encodePtrBytes (M := M) pv addr 8 a t).symm)

/-- The `BasicMemory`-specialized `encode_ptr` agrees with `Trusted` as well. -/
theorem encodePtr_proj (addr a t : Nat) (h : addr < 2 ^ 64) :
    Interp.encodePtr { addr := (addr : Int), provenance := some (bmProv a t) } =
      .ok (projBytes bmProv (encodePtrBytes addr 8 a t)) :=
  (encodePtr_of_encode { addr := (addr : Int), provenance := some (bmProv a t) }
      (Interp.leBytes addr 8) (endianness_encode_ptr addr h)).trans
    (congrArg Except.ok ((encodePtrBytes_eq_M _ _ 0).trans
      (proj_encodePtrBytes (M := Interp.BM) bmProv addr 8 a t).symm))

/-- The `Trusted` untyped encoding of a pointer value is `encodePtrBytes`. -/
theorem encodeUntyped_ptr (fuel : Nat) (p : ProvenancePtr) (sz : Nat) (hsz : 0 < sz) :
    encodeUntypedValueToBytes (fuel + 1) (.ptr p sz) =
      some (encodePtrBytes p.offsetBytes sz p.allocId p.tag) := by
  cases sz with
  | zero => omega
  | succ n => rfl

/-- **`encodeValueToBytes` on thin pointers.** For any thin pointer type (`.rawPtr`, `.ref`,
`.fnPtr`) at target pointer width `pb > 0`, `encodeValueToBytes` produces `encodePtrBytes`. -/
theorem encodeValueToBytes_thinPtr (fuel : Nat) (layouts : LayoutTable) (ty : Ty)
    (p : ProvenancePtr) (pb : Nat) (hpb : layoutPointerBytes layouts = pb) (h0 : 0 < pb)
    (hty : (∃ m pt, ty.kind = .rawPtr m pt ∧ thinPointee pt = true) ∨
           (∃ m pt, ty.kind = .ref m pt ∧ thinPointee pt = true) ∨
           (∃ a r s ab, ty.kind = .fnPtr a r s ab)) :
    encodeValueToBytes (fuel + 1) layouts ty (.ptr p pb) =
      some (encodePtrBytes p.offsetBytes pb p.allocId p.tag) := by
  obtain ⟨kind, lidx⟩ := ty
  have hblt : Nat.blt 0 pb = true := by rw [Nat.blt_eq]; exact h0
  have hnz : Nat.beq pb 0 = false := by cases pb with | zero => omega | succ _ => rfl
  rcases hty with ⟨m, pt, hk, hthin⟩ | ⟨m, pt, hk, hthin⟩ | ⟨a, r, s, ab, hk⟩
  · dsimp only at hk; subst hk
    cases pt <;> first
      | (cases hthin; done)
      | (unfold encodeValueToBytes; rw [hpb]; simp [hblt, encodeScalarBytes, hnz, encodeLittleEndianBytes])
  · dsimp only at hk; subst hk
    cases pt <;> first
      | (cases hthin; done)
      | (unfold encodeValueToBytes; rw [hpb]; simp [hblt, encodeScalarBytes, hnz, encodeLittleEndianBytes])
  · dsimp only at hk; subst hk
    unfold encodeValueToBytes; rw [hpb]; simp [hblt, encodeScalarBytes, hnz, encodeLittleEndianBytes]

theorem bits_encodeAux (a t o pb : Nat) :
    ∀ (n bits idx : Nat),
      decodeLittleEndianBits (encodePtrBytesAux a t o pb bits idx n) = some (bits % 256 ^ n)
  | 0, bits, _ => by
      show some 0 = some (bits % 256 ^ 0)
      rw [Nat.pow_zero, Nat.mod_one]
  | n + 1, bits, idx => by
      have ih := bits_encodeAux a t o pb n (bits / 256) (idx + 1)
      show (match decodeLittleEndianBits
            (encodePtrBytesAux a t o pb (bits / 256) (idx + 1) n) with
        | some highBits =>
          some (Nat.add (UInt8.ofNat bits).toBitVec.toNat (Nat.mul 256 highBits))
        | none => none) = some (bits % 256 ^ (n + 1))
      rw [ih]
      show some ((UInt8.ofNat bits).toNat + 256 * (bits / 256 % 256 ^ n)) =
        some (bits % 256 ^ (n + 1))
      rw [u8_ofNat_toNat, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]

theorem trCoh_encodeAux (a t o pb : Nat) :
    ∀ (n bits idx : Nat), idx + n = pb →
      TrCoh a t o pb idx (encodePtrBytesAux a t o pb bits idx n)
  | 0, _, idx, h => by
      show idx = pb
      omega
  | n + 1, bits, idx, h =>
      And.intro ⟨_, rfl⟩
        (trCoh_encodeAux a t o pb n (bits / 256) (idx + 1) (by omega))

/-- The `Trusted` encoding of a pointer is coherent, with the head fragment of the pointer. -/
theorem coherent?_encodePtrBytes (bits pb a t : Nat) (hpb : 0 < pb) :
    abstractBytesCoherentPtrProv? (encodePtrBytes bits pb a t) =
      some ⟨a, t, 0, normPtrByteOffset pb bits, pb⟩ :=
  (coherent?_eq_some_iff _ _).mpr ⟨hpb, rfl, trCoh_encodeAux a t _ pb pb bits 0 (by omega)⟩

theorem encodePtrBytes_length (bits pb a t : Nat) : (encodePtrBytes bits pb a t).length = pb := by
  have := trCoh_length a t _ pb _ 0 (trCoh_encodeAux a t (normPtrByteOffset pb bits) pb pb bits 0
    (by omega))
  rw [Nat.zero_add] at this
  exact this

/-- Every byte of an encoded pointer is the fragment of its own position. -/
theorem encodePtrBytes_get (bits pb a t i : Nat) (b : AbstractByte)
    (h : (encodePtrBytes bits pb a t)[i]? = some b) :
    ∃ v, b = .init v (some ⟨a, t, i, normPtrByteOffset pb bits, pb⟩) := by
  have := trCoh_get a t _ pb _ 0
    (trCoh_encodeAux a t (normPtrByteOffset pb bits) pb pb bits 0 (by omega)) i b h
  rw [Nat.zero_add] at this
  exact this

/-- **Intact `Trusted` round trip** (`encodePtrBytes → decodePtrBytesNoForge`), for
raw pointers and references, at any positive pointer width. -/
theorem thinDecode_encodePtrBytes (isRef : Bool) (bits pb a t : Nat) (hpb : 0 < pb) :
    thinDecode isRef pb (encodePtrBytes bits pb a t) =
      some (.ptr { allocId := a, offsetBytes := bits % 256 ^ pb } pb) :=
  thinDecode_coherent isRef pb _ _ ⟨a, t, 0, normPtrByteOffset pb bits, pb⟩ hpb
    (encodePtrBytes_length bits pb a t) (bits_encodeAux a t _ pb pb bits 0)
    (coherent?_encodePtrBytes bits pb a t hpb) rfl

/-- **Intact MiniRust round trip on the projected `Trusted` encoding.** For every
valid 64-bit pointer, MiniRust `decode_ptr` of the projected `Trusted` bytes is
the same address with the projected provenance. -/
theorem decodePtrM_proj_encodePtrBytes {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (addr a t : Nat) (h : addr < 2 ^ 64) :
    Interp.decodePtrM (M := M) (projBytes pv (encodePtrBytes addr 8 a t)) =
      .ok (some { addr := (addr : Int), provenance := some (pv a t) }) := by
  obtain ⟨data, hd, _, hm⟩ := coherent_decode_agreement (M := M) pv (encodePtrBytes addr 8 a t)
    ⟨a, t, 0, normPtrByteOffset 8 addr, 8⟩ false (encodePtrBytes_length addr 8 a t)
    (coherent?_encodePtrBytes addr 8 a t (by decide)) rfl
  have hbits : some (Interp.leValue data) = some (addr % 256 ^ 8) := by
    have h1 := bits_eq_leValue (encodePtrBytes addr 8 a t)
    rw [hd, bits_encodeAux a t _ 8 8 addr 0] at h1
    exact h1.symm
  injection hbits with hbits
  have hmod : addr % 256 ^ 8 = addr := Nat.mod_eq_of_lt (by
    have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    omega)
  rw [hm, hbits, hmod]

/-- **Union raw-byte carrier round trip**: the lossless `Value` carrier of an
abstract byte decodes back to exactly that byte. -/
theorem rawCarrier_roundtrip (b : AbstractByte) :
    decodeRawAbstractByteVal? (encodeRawAbstractByteVal b) = some b := by
  cases b with
  | uninit => rfl
  | init v pr =>
      cases pr with
      | none =>
          show decodeRawAbstractByteVal? (.scalar ⟨v.toBitVec.toNat, 1⟩) = _
          have hv : UInt8.ofNat v.toBitVec.toNat = v := UInt8.ofNat_toNat
          unfold decodeRawAbstractByteVal?
          split <;> simp_all <;> (rename_i hbits; subst hbits; exact UInt8.ofNat_toNat)
      | some f =>
          show some (AbstractByte.init (UInt8.ofNat v.toBitVec.toNat) (some _)) = _
          have hv : UInt8.ofNat v.toBitVec.toNat = v := UInt8.ofNat_toNat
          rw [hv]

theorem rawCarrier_list_roundtrip :
    ∀ bs : List AbstractByte,
      decodeRawAbstractByteVals? (bs.map encodeRawAbstractByteVal) = some bs
  | [] => rfl
  | b :: rest => by
      show (match decodeRawAbstractByteVal? (encodeRawAbstractByteVal b),
          decodeRawAbstractByteVals? (rest.map encodeRawAbstractByteVal) with
        | some b', some bs' => some (b' :: bs')
        | _, _ => none) = some (b :: rest)
      rw [rawCarrier_roundtrip, rawCarrier_list_roundtrip rest]

/-- **Intact bytewise copy through the union raw-byte carrier.** A pointer moved
byte by byte through the carrier (`[u8; 8]`, `MaybeUninit`, or a union) decodes,
in both authorities, to exactly the original address and provenance. -/
theorem rawCarrier_ptr_roundtrip {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (isRef : Bool) (addr a t : Nat)
    (h : addr < 2 ^ 64) :
    ∃ bs, decodeRawAbstractByteVals?
        ((encodePtrBytes addr 8 a t).map encodeRawAbstractByteVal) = some bs ∧
      thinDecode isRef 8 bs = some (.ptr { allocId := a, offsetBytes := addr } 8) ∧
      Interp.decodePtrM (M := M) (projBytes pv bs) =
        .ok (some { addr := (addr : Int), provenance := some (pv a t) }) := by
  refine ⟨_, rawCarrier_list_roundtrip _, ?_, decodePtrM_proj_encodePtrBytes pv addr a t h⟩
  have hmod : addr % 256 ^ 8 = addr := Nat.mod_eq_of_lt (by
    have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    omega)
  have := thinDecode_encodePtrBytes isRef addr 8 a t (by decide)
  rw [hmod] at this
  exact this

/-! ### §6. `UCG#558` W1: both authorities strip provenance on every non-intact stream -/

/-- **Arbitrary non-identity permutation (`Trusted`).** A stream holding at
position `i` the byte that an encoded pointer carries at a different position
`j` has no coherent provenance. -/
theorem permuted_strips_trusted (bs : List AbstractByte) (bits pb a t i j : Nat)
    (b : AbstractByte) (hij : i ≠ j) (hb : bs[i]? = some b)
    (hj : (encodePtrBytes bits pb a t)[j]? = some b) :
    abstractBytesCoherentPtrProv? bs = none := by
  obtain ⟨v, hv⟩ := encodePtrBytes_get bits pb a t j b hj
  subst hv
  refine coherent?_none_of_bad_position bs i _ hb ?_
  intro v' f hf
  injection hf with _ hf
  injection hf with hf
  subst hf
  exact fun h => hij h.symm

/-- **Arbitrary non-identity permutation (MiniRust).** The projected stream loses
its provenance in `decode_ptr` as well. -/
theorem permuted_strips_minirust {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte)
    (bits pb a t i j : Nat) (b : AbstractByte) (hij : i ≠ j) (hb : bs[i]? = some b)
    (hj : (encodePtrBytes bits pb a t)[j]? = some b) :
    mrProvM M (projBytes pv bs) = none := by
  obtain ⟨v, hv⟩ := encodePtrBytes_get bits pb a t j b hj
  subst hv
  refine mrProvM_eq_none_of_bad _ i _ (projBytes_get pv bs i _ hb) ?_
  intro v' fr hf
  have hf' : Gen.AbstractByte.Init v
      (some (projFrag pv ⟨a, t, j, normPtrByteOffset pb bits, pb⟩)) = .Init v' (some fr) := hf
  injection hf' with _ hf'
  injection hf' with hf'
  subst hf'
  show ((j : Nat) : Int) ≠ (i : Int)
  omega

/-- Swap of byte 0 and byte 1. -/
def swap01 : List AbstractByte → List AbstractByte
  | x :: y :: rest => y :: x :: rest
  | bs => bs

/-- Byte 0 repeated over the whole stream. -/
def dupHead : List AbstractByte → List AbstractByte
  | x :: rest => x :: rest.map (fun _ => x)
  | [] => []

/-- **8-byte full reversal** strips provenance in both authorities, for every
address (including the all-zero image of offset `0`) and provenance. -/
theorem reversal_strips {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bits a t : Nat) :
    abstractBytesCoherentPtrProv? (encodePtrBytes bits 8 a t).reverse = none ∧
      mrProvM M (projBytes pv (encodePtrBytes bits 8 a t).reverse) = none :=
  ⟨permuted_strips_trusted _ bits 8 a t 0 7 _ (by decide) rfl rfl,
   permuted_strips_minirust pv _ bits 8 a t 0 7 _ (by decide) rfl rfl⟩

/-- **Byte-0 / byte-1 swap** strips provenance in both authorities. -/
theorem swap01_strips {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bits a t : Nat) :
    abstractBytesCoherentPtrProv? (swap01 (encodePtrBytes bits 8 a t)) = none ∧
      mrProvM M (projBytes pv (swap01 (encodePtrBytes bits 8 a t))) = none :=
  ⟨permuted_strips_trusted _ bits 8 a t 0 1 _ (by decide) rfl rfl,
   permuted_strips_minirust pv _ bits 8 a t 0 1 _ (by decide) rfl rfl⟩

/-- **Byte 0 duplicated 8×** strips provenance in both authorities. -/
theorem dupHead_strips {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bits a t : Nat) :
    abstractBytesCoherentPtrProv? (dupHead (encodePtrBytes bits 8 a t)) = none ∧
      mrProvM M (projBytes pv (dupHead (encodePtrBytes bits 8 a t))) = none :=
  ⟨permuted_strips_trusted _ bits 8 a t 1 0 _ (by decide) rfl rfl,
   permuted_strips_minirust pv _ bits 8 a t 1 0 _ (by decide) rfl rfl⟩

/-- **End-to-end decoder stripping (`UCG#558` W1)** for full reversal, byte-0/1 swap, and head
duplication: `Trusted` decodes raw pointers to provenance-free `.scalar` and rejects references
(`none`), while MiniRust `decodePtrM` returns `.ok (some ⟨addr, none⟩)`. -/
theorem w1_transforms_decode_strips {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bits a t : Nat) :
    let bsRev := (encodePtrBytes bits 8 a t).reverse
    let bsSwap := swap01 (encodePtrBytes bits 8 a t)
    let bsDup := dupHead (encodePtrBytes bits 8 a t)
    (∃ d, trData bsRev = some d ∧ thinDecode false 8 bsRev = some (.scalar ⟨Interp.leValue d, 8⟩) ∧
      thinDecode true 8 bsRev = none ∧
      Interp.decodePtrM (M := M) (projBytes pv bsRev) =
        .ok (some { addr := ((Interp.leValue d : Nat) : Int), provenance := none })) ∧
    (∃ d, trData bsSwap = some d ∧ thinDecode false 8 bsSwap = some (.scalar ⟨Interp.leValue d, 8⟩) ∧
      thinDecode true 8 bsSwap = none ∧
      Interp.decodePtrM (M := M) (projBytes pv bsSwap) =
        .ok (some { addr := ((Interp.leValue d : Nat) : Int), provenance := none })) ∧
    (∃ d, trData bsDup = some d ∧ thinDecode false 8 bsDup = some (.scalar ⟨Interp.leValue d, 8⟩) ∧
      thinDecode true 8 bsDup = none ∧
      Interp.decodePtrM (M := M) (projBytes pv bsDup) =
        .ok (some { addr := ((Interp.leValue d : Nat) : Int), provenance := none })) := by
  intro bsRev bsSwap bsDup
  have hstep : ∀ (bs : List AbstractByte) (data : List UInt8),
      bs.length = 8 → trData bs = some data →
      abstractBytesCoherentPtrProv? bs = none →
      mrProvM M (projBytes pv bs) = none →
      ∃ d, trData bs = some d ∧ thinDecode false 8 bs = some (.scalar ⟨Interp.leValue d, 8⟩) ∧
        thinDecode true 8 bs = none ∧
        Interp.decodePtrM (M := M) (projBytes pv bs) =
          .ok (some { addr := ((Interp.leValue d : Nat) : Int), provenance := none }) := by
    intro bs data hlen hd htr hmr
    have hbits : decodeLittleEndianBits bs = some (Interp.leValue data) := by
      rw [bits_eq_leValue, hd]; rfl
    refine ⟨data, hd, thinDecode_raw_incoherent 8 bs _ (by decide) hlen hbits htr,
      thinDecode_ref_incoherent 8 bs htr, ?_⟩
    rw [decodePtrM_proj pv bs hlen, hd, hmr]; rfl
  refine ⟨?_, ?_, ?_⟩
  · exact hstep bsRev _ rfl rfl (reversal_strips (M := M) pv bits a t).1 (reversal_strips (M := M) pv bits a t).2
  · exact hstep bsSwap _ rfl rfl (swap01_strips (M := M) pv bits a t).1 (swap01_strips (M := M) pv bits a t).2
  · exact hstep bsDup _ rfl rfl (dupHead_strips (M := M) pv bits a t).1 (dupHead_strips (M := M) pv bits a t).2

/-- **Mixed provenance** (`Trusted`): fragments of two allocations or two tags. -/
theorem mixed_provenance_strips_trusted (bs : List AbstractByte) (i j : Nat) (vi vj : UInt8)
    (fi fj : PtrByteFrag)
    (hi : bs[i]? = some (.init vi (some fi))) (hj : bs[j]? = some (.init vj (some fj)))
    (hne : fi.allocId ≠ fj.allocId ∨ fi.tag ≠ fj.tag) :
    abstractBytesCoherentPtrProv? bs = none :=
  coherent?_none_of_field_mismatch bs i j vi vj fi fj hi hj
    (hne.elim Or.inl (fun h => Or.inr (Or.inl h)))

/-- **Mixed provenance** (MiniRust): fragments whose projected provenances differ. -/
theorem mixed_provenance_strips_minirust {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte) (i j : Nat)
    (vi vj : UInt8) (fi fj : PtrByteFrag)
    (hi : bs[i]? = some (.init vi (some fi))) (hj : bs[j]? = some (.init vj (some fj)))
    (hne : pv fi.allocId fi.tag ≠ pv fj.allocId fj.tag) :
    mrProvM M (projBytes pv bs) = none :=
  mrProvM_eq_none_of_prov_mismatch _ i j vi vj (projFrag pv fi) (projFrag pv fj)
    (projBytes_get pv bs i _ hi) (projBytes_get pv bs j _ hj) hne

/-- **Missing provenance** (`Trusted`): a plain byte anywhere in the stream (in
particular an all-plain integer image) never yields provenance — no
integer-to-pointer forging. -/
theorem missing_provenance_strips_trusted (bs : List AbstractByte) (i : Nat) (v : UInt8)
    (hb : bs[i]? = some (.init v none)) :
    abstractBytesCoherentPtrProv? bs = none := by
  refine coherent?_none_of_bad_position bs i _ hb ?_
  intro v' f hf
  injection hf with _ hf
  cases hf

/-- **Missing provenance** (MiniRust). -/
theorem missing_provenance_strips_minirust {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte) (i : Nat) (v : UInt8)
    (hb : bs[i]? = some (.init v none)) :
    mrProvM M (projBytes pv bs) = none := by
  refine mrProvM_eq_none_of_bad _ i _ (projBytes_get pv bs i _ hb) ?_
  intro v' fr hf
  have hf' : Gen.AbstractByte.Init v (none : Option (Gen.ProvenanceFrag (Gen.Memory.Provenance M))) =
      .Init v' (some fr) := hf
  injection hf' with _ hf'
  cases hf'

/-- **Any `.uninit` byte** (`Trusted`): the pointer decode fails, for raw pointers
and references alike. -/
theorem uninit_rejected_trusted (isRef : Bool) (pb : Nat) (bs : List AbstractByte)
    (h : AbstractByte.uninit ∈ bs) : thinDecode isRef pb bs = none := by
  refine thinDecode_uninit isRef pb bs ?_
  rw [bits_eq_leValue, trData_none_of_uninit bs h]
  rfl

/-- **Any `.uninit` byte** (MiniRust): `decode_ptr` returns `None`. -/
theorem uninit_rejected_minirust {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte) (hlen : bs.length = 8)
    (h : AbstractByte.uninit ∈ bs) :
    Interp.decodePtrM (M := M) (projBytes pv bs) = .ok none := by
  rw [decodePtrM_proj pv bs hlen, trData_none_of_uninit bs h]
  rfl

/-! ### §7. `UCG#558` W2 / `rust#148259`: offset splices and the strict refinement -/

/-- **`Trusted` strips an offset splice.** A stream holding byte `i` of the
encoding of `bits₁` and byte `j` of the encoding of `bits₂` — the *same*
allocation and tag — has no coherent provenance when the two normalized
originating offsets differ. -/
theorem offset_splice_trusted_strips (bs : List AbstractByte) (bits₁ bits₂ pb a t i j : Nat)
    (b₁ b₂ : AbstractByte)
    (h₁ : bs[i]? = some b₁) (e₁ : (encodePtrBytes bits₁ pb a t)[i]? = some b₁)
    (h₂ : bs[j]? = some b₂) (e₂ : (encodePtrBytes bits₂ pb a t)[j]? = some b₂)
    (hne : normPtrByteOffset pb bits₁ ≠ normPtrByteOffset pb bits₂) :
    abstractBytesCoherentPtrProv? bs = none := by
  obtain ⟨v₁, hv₁⟩ := encodePtrBytes_get bits₁ pb a t i b₁ e₁
  obtain ⟨v₂, hv₂⟩ := encodePtrBytes_get bits₂ pb a t j b₂ e₂
  subst hv₁
  subst hv₂
  exact coherent?_none_of_field_mismatch bs i j v₁ v₂ _ _ h₁ h₂ (Or.inr (Or.inr (Or.inl hne)))

/-- **Vendored MiniRust retains provenance on every same-provenance splice.** A
non-empty stream each of whose bytes is the in-position byte of the encoding of
`bits₁` or of `bits₂` (same allocation and tag) keeps `some (pv a t)` in
`decode_ptr`: MiniRust's `ProvenanceFrag { provenance, position }` cannot tell
the two originating pointers apart. -/
theorem offset_splice_minirust_retains {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte)
    (bits₁ bits₂ pb a t : Nat) (hne : bs ≠ [])
    (hsel : ∀ (i : Nat) (b : AbstractByte), bs[i]? = some b →
      (encodePtrBytes bits₁ pb a t)[i]? = some b ∨ (encodePtrBytes bits₂ pb a t)[i]? = some b) :
    mrProvM M (projBytes pv bs) = some (pv a t) := by
  refine mrProvM_eq_some_of_get _ _ ?_ ?_
  · intro h
    have hl := congrArg List.length h
    rw [projBytes_length] at hl
    cases bs with
    | nil => exact hne rfl
    | cons _ _ => cases hl
  · intro i b' hb'
    cases hbi : bs[i]? with
    | none =>
        have := projBytes_get pv bs i
        unfold projBytes at hb'
        rw [List.getElem?_map, hbi] at hb'
        cases hb'
    | some b =>
        have hp := projBytes_get pv bs i b hbi
        rw [hp] at hb'
        injection hb' with hb'
        subst hb'
        rcases hsel i b hbi with h | h
        · obtain ⟨v, hv⟩ := encodePtrBytes_get bits₁ pb a t i b h
          subst hv
          exact ⟨v, rfl⟩
        · obtain ⟨v, hv⟩ := encodePtrBytes_get bits₂ pb a t i b h
          subst hv
          exact ⟨v, rfl⟩

/-- **End-to-end offset-splice decoder divergence (`DIV-MR-OFFSET-SPLICE`, `UCG#558` W2).**
For any 8-byte same-provenance splice `bs` drawing each byte in-position from `bits₁` or `bits₂`
(with at least one byte from each and `normPtrByteOffset 8 bits₁ ≠ normPtrByteOffset 8 bits₂`):
`Trusted` strips provenance (`thinDecode false` → `.scalar`, `thinDecode true` → `none`), while
MiniRust `decodePtrM` retains `some (pv a t)` on the exact same decoded address. -/
theorem offset_splice_decode_divergence {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte)
    (bits₁ bits₂ a t i j : Nat) (b₁ b₂ : AbstractByte) (hlen : bs.length = 8)
    (hsel : ∀ (k : Nat) (b : AbstractByte), bs[k]? = some b →
      (encodePtrBytes bits₁ 8 a t)[k]? = some b ∨ (encodePtrBytes bits₂ 8 a t)[k]? = some b)
    (h₁ : bs[i]? = some b₁) (e₁ : (encodePtrBytes bits₁ 8 a t)[i]? = some b₁)
    (h₂ : bs[j]? = some b₂) (e₂ : (encodePtrBytes bits₂ 8 a t)[j]? = some b₂)
    (hne : normPtrByteOffset 8 bits₁ ≠ normPtrByteOffset 8 bits₂) :
    ∃ data, trData bs = some data ∧
      thinDecode false 8 bs = some (.scalar ⟨Interp.leValue data, 8⟩) ∧
      thinDecode true 8 bs = none ∧
      Interp.decodePtrM (M := M) (projBytes pv bs) =
        .ok (some { addr := ((Interp.leValue data : Nat) : Int),
                    provenance := some (pv a t) }) := by
  have htr := offset_splice_trusted_strips bs bits₁ bits₂ 8 a t i j b₁ b₂ h₁ e₁ h₂ e₂ hne
  have hneList : bs ≠ [] := by intro h; subst h; cases hlen
  have hmr := offset_splice_minirust_retains (M := M) pv bs bits₁ bits₂ 8 a t hneList hsel
  have hdata : ∃ data, trData bs = some data := by
    have hall : ∀ (k : Nat) (b : AbstractByte), bs[k]? = some b → ∃ (v : UInt8) (pr : Option PtrByteFrag), b = .init v pr := by
      intro k b hk
      rcases hsel k b hk with h | h
      · obtain ⟨v, hv⟩ := encodePtrBytes_get bits₁ 8 a t k b h; exact ⟨v, _, hv⟩
      · obtain ⟨v, hv⟩ := encodePtrBytes_get bits₂ 8 a t k b h; exact ⟨v, _, hv⟩
    have aux : ∀ (l : List AbstractByte),
        (∀ (k : Nat) (b : AbstractByte), l[k]? = some b → ∃ (v : UInt8) (pr : Option PtrByteFrag), b = .init v pr) → ∃ d, trData l = some d := by
      intro l
      induction l with
      | nil => intro _; exact ⟨[], rfl⟩
      | cons x xs ih =>
        intro hl
        obtain ⟨v, pr, rfl⟩ := hl 0 x rfl
        obtain ⟨d, hd⟩ := ih (fun k b hk => hl (k + 1) b hk)
        exact ⟨v :: d, by show (trData xs).map (v :: ·) = _; rw [hd]; rfl⟩
    exact aux bs hall
  obtain ⟨data, hd⟩ := hdata
  have hbits : decodeLittleEndianBits bs = some (Interp.leValue data) := by
    rw [bits_eq_leValue, hd]; rfl
  refine ⟨data, hd, thinDecode_raw_incoherent 8 bs _ (by decide) hlen hbits htr,
    thinDecode_ref_incoherent 8 bs htr, ?_⟩
  rw [decodePtrM_proj pv bs hlen, hd, hmr]
  rfl

/-- **Exact characterization of the refinement gap.** For an injective
provenance embedding, whenever MiniRust retains provenance on the projected
stream, `Trusted` strips it **if and only if** two fragments disagree on the
originating offset or the pointer width, or the fragment width is not the
stream length. (With a common width — every pointer of one target — the
converse of `trusted_retains_implies_minirust_retains` therefore fails
precisely on same-provenance splices of different originating offsets.) -/
theorem converse_gap_iff {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M)
    (hinj : ∀ a t a' t', pv a t = pv a' t' → a = a' ∧ t = t')
    (bs : List AbstractByte) (p : Gen.Memory.Provenance M)
    (hmr : mrProvM M (projBytes pv bs) = some p) :
    abstractBytesCoherentPtrProv? bs = none ↔
      ∃ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag), bs[i]? = some (.init vi (some fi)) ∧
        bs[j]? = some (.init vj (some fj)) ∧
        (fi.origOffset ≠ fj.origOffset ∨ fi.ptrBytes ≠ fj.ptrBytes ∨
          fi.ptrBytes ≠ bs.length) := by
  constructor
  · intro hnone
    apply Classical.byContradiction
    intro hno
    obtain ⟨hne, hcoh⟩ := (mrProvM_eq_some_iff _ _).mp hmr
    have hget := (mrCoh_iff_get p _ 0).mp hcoh
    have hall : ∀ (i : Nat) (b : AbstractByte), bs[i]? = some b →
        ∃ (v : UInt8) (f : PtrByteFrag),
          b = AbstractByte.init v (some f) ∧ pv f.allocId f.tag = p ∧ f.byteIdx = i := by
      intro i b hb
      obtain ⟨v, hv⟩ := hget i _ (projBytes_get pv bs i b hb)
      obtain ⟨f, hf, hfr⟩ := projByte_eq_init_some pv b v _ hv
      refine ⟨v, f, hf, congrArg Gen.ProvenanceFrag.provenance hfr, ?_⟩
      have hpos : ((f.byteIdx : Nat) : Int) = ((0 + i : Nat) : Int) :=
        congrArg Gen.ProvenanceFrag.position hfr
      omega
    cases bs with
    | nil => exact hne rfl
    | cons b0 rest =>
        obtain ⟨v0, f0, hf0, hp0, hi0⟩ := hall 0 b0 rfl
        subst hf0
        have hfields : ∀ (i : Nat) (b : AbstractByte),
            (AbstractByte.init v0 (some f0) :: rest)[i]? = some b →
            ∃ v, b = AbstractByte.init v
              (some ⟨f0.allocId, f0.tag, 0 + i, f0.origOffset, f0.ptrBytes⟩) := by
          intro i b hb
          obtain ⟨v, f, hf, hp, hi⟩ := hall i b hb
          subst hf
          obtain ⟨ha, ht⟩ := hinj _ _ _ _ (hp.trans hp0.symm)
          have ho : f.origOffset = f0.origOffset :=
            Decidable.byContradiction fun hne' =>
              hno ⟨i, 0, v, v0, f, f0, hb, rfl, Or.inl hne'⟩
          have hw : f.ptrBytes = f0.ptrBytes :=
            Decidable.byContradiction fun hne' =>
              hno ⟨i, 0, v, v0, f, f0, hb, rfl, Or.inr (Or.inl hne')⟩
          refine ⟨v, congrArg (fun x => AbstractByte.init v (some x)) (frag_ext _ _ ha ht ?_ ho hw)⟩
          show f.byteIdx = 0 + i
          omega
        have hlen : f0.ptrBytes = (AbstractByte.init v0 (some f0) :: rest).length :=
          Decidable.byContradiction fun hne' =>
            hno ⟨0, 0, v0, v0, f0, f0, rfl, rfl, Or.inr (Or.inr hne')⟩
        have hc := trCoh_of_get f0.allocId f0.tag f0.origOffset f0.ptrBytes _ 0 (by omega) hfields
        have hpos : 0 < f0.ptrBytes := by
          simp only [List.length_cons] at hlen
          omega
        have hsome := (coherent?_eq_some_iff _ f0).mpr ⟨hpos, hi0, hc⟩
        rw [hnone] at hsome
        cases hsome
  · rintro ⟨i, j, vi, vj, fi, fj, hi, hj, hne⟩
    cases h : abstractBytesCoherentPtrProv? bs with
    | none => rfl
    | some f =>
        obtain ⟨_, _, hc⟩ := (coherent?_eq_some_iff bs f).mp h
        obtain ⟨v1, h1⟩ := trCoh_get _ _ _ _ bs 0 hc i _ hi
        obtain ⟨v2, h2⟩ := trCoh_get _ _ _ _ bs 0 hc j _ hj
        have hl := trCoh_length _ _ _ _ bs 0 hc
        injection h1 with _ h1
        injection h1 with h1
        injection h2 with _ h2
        injection h2 with h2
        subst h1
        subst h2
        rcases hne with h | h | h
        · exact absurd rfl h
        · exact absurd rfl h
        · exact absurd (by show f.ptrBytes = bs.length; omega) h

/-! ### §8. Wide pointers -/

theorem take_append :
    ∀ (d m : List AbstractByte), takeAbstractBytes d.length (d ++ m) = d
  | [], m => by cases m <;> rfl
  | x :: d, m => by
      show x :: takeAbstractBytes d.length (d ++ m) = x :: d
      rw [take_append d m]

theorem drop_append :
    ∀ (d m : List AbstractByte), dropAbstractBytes d.length (d ++ m) = m
  | [], _ => rfl
  | _ :: d, m => drop_append d m

/-- The slice / `str` metadata half of `decodePtrBytesNoForge`: a plain integer
length; any provenance-carrying byte is rejected. -/
def sliceMetaDecode (pb : Nat) (metaBytes : List AbstractByte) : Option Value :=
  match decodeLittleEndianBits metaBytes with
  | .none => .none
  | .some metaBits =>
    match abstractBytesHaveProv metaBytes with
    | true => .none
    | false => .some (.scalar ⟨metaBits, pb⟩)

/-- **Wide slice pointers** (`&[T]`, `*const [T]`): the data half is decoded by
`thinDecode` and the length half by `sliceMetaDecode`. -/
theorem decodePtrBytesNoForge_slice (isRef : Bool) (elem : RigidTy) (d m : List AbstractByte)
    (h0 : 0 < d.length) (hm : m.length = d.length) :
    decodePtrBytesNoForge isRef (.slice elem) d.length (d ++ m) =
      (match thinDecode isRef d.length d, sliceMetaDecode d.length m with
       | some dv, some mv => some (.aggregate 0 [dv, mv])
       | _, _ => none) := by
  have e1 : Nat.blt 0 d.length = true := by
    rw [Nat.blt_eq]
    exact h0
  have e2 : Nat.beq (length (d ++ m)) (Nat.add d.length d.length) = true :=
    (nat_beq_iff _ _).mpr (by
      show (d ++ m).length = d.length + d.length
      rw [List.length_append, hm])
  unfold decodePtrBytesNoForge thinDecode
  simp only [e1, e2, take_append, drop_append]
  rfl

/-- **Wide `str` pointers** (`&str`, `*const str`) decode exactly as slices. -/
theorem decodePtrBytesNoForge_str (isRef : Bool) (d m : List AbstractByte)
    (h0 : 0 < d.length) (hm : m.length = d.length) :
    decodePtrBytesNoForge isRef .str d.length (d ++ m) =
      (match thinDecode isRef d.length d, sliceMetaDecode d.length m with
       | some dv, some mv => some (.aggregate 0 [dv, mv])
       | _, _ => none) := by
  have e1 : Nat.blt 0 d.length = true := by
    rw [Nat.blt_eq]
    exact h0
  have e2 : Nat.beq (length (d ++ m)) (Nat.add d.length d.length) = true :=
    (nat_beq_iff _ _).mpr (by
      show (d ++ m).length = d.length + d.length
      rw [List.length_append, hm])
  unfold decodePtrBytesNoForge thinDecode
  simp only [e1, e2, take_append, drop_append]
  rfl

/-- **Provenance-bearing slice metadata is rejected** — in particular the
swapped halves `metadata ++ data` of a wide pointer, whose "length" half is a
pointer image (`DIV-MR-PTR2INT`: MiniRust accepts it as an integer). -/
theorem slice_meta_with_provenance_rejected (isRef : Bool) (elem : RigidTy)
    (d m : List AbstractByte) (h0 : 0 < d.length) (hm : m.length = d.length)
    (hp : abstractBytesHaveProv m = true) :
    decodePtrBytesNoForge isRef (.slice elem) d.length (d ++ m) = none := by
  rw [decodePtrBytesNoForge_slice isRef elem d m h0 hm]
  unfold sliceMetaDecode
  rw [hp]
  cases thinDecode isRef d.length d <;> cases decodeLittleEndianBits m <;> rfl

/-- **Wide trait-object pointers (`&dyn Trait`, `*const dyn Trait`)**: both data and vtable halves
decode through `thinDecode`. -/
theorem decodePtrBytesNoForge_dyn (isRef : Bool) (tr : String) (d m : List AbstractByte)
    (h0 : 0 < d.length) (hm : m.length = d.length) :
    decodePtrBytesNoForge isRef (.dynamic tr) d.length (d ++ m) =
      (match thinDecode isRef d.length d, thinDecode isRef d.length m with
       | some dv, some mv => some (.aggregate 0 [dv, mv])
       | _, _ => none) := by
  have e1 : Nat.blt 0 d.length = true := by rw [Nat.blt_eq]; exact h0
  have e2 : Nat.beq (length (d ++ m)) (Nat.add d.length d.length) = true :=
    (nat_beq_iff _ _).mpr (by show (d ++ m).length = d.length + d.length; rw [List.length_append, hm])
  have e3 : Nat.beq (length m) d.length = true := (nat_beq_iff _ _).mpr hm
  unfold decodePtrBytesNoForge thinDecode
  simp only [e1, e2, e3, take_append, drop_append]
  cases decodeLittleEndianBits m <;> rfl

/-- **Exact wide slice/`str` encoding correspondence.** MiniRust `encodeWidePtrM .ElementCount`
produces the exact projection of `encodePtrBytes addr 8 a t ++ encodePlainLittleEndianBytes len 8`. -/
theorem encodeWidePtrM_slice_proj {M : Type} [Gen.Memory M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (addr len a t : Nat)
    (ha : addr < 2 ^ 64) (hl : len < 2 ^ 64) :
    Interp.encodeWidePtrM (M := M) .ElementCount
      { thin_pointer := { addr := (addr : Int), provenance := some (pv a t) },
        metadata := some (.ElementCount (len : Int)) } =
      .ok (projBytes pv (encodePtrBytes addr 8 a t ++ encodePlainLittleEndianBytes len 8)) := by
  rw [encodeWidePtrM_slice_eq addr len (some (pv a t)) ha hl]
  unfold projBytes
  rw [List.map_append]
  change Except.ok _ = Except.ok (projBytes pv (encodePtrBytes addr 8 a t) ++
    projBytes pv (encodePlainLittleEndianBytes len 8))
  rw [proj_encodePtrBytes (M := M) pv addr 8 a t, proj_plain_bytes (M := M) pv 8 len 0]

/-- **Exact wide `&dyn Trait` encoding correspondence.** MiniRust `encodeWidePtrM (.VTablePointer tr)`
produces the exact projection of `encodePtrBytes addr 8 a t ++ encodePtrBytes vtAddr 8 va vt`. -/
theorem encodeWidePtrM_dyn_proj {M : Type} [Gen.Memory M] (tr : Gen.TraitName)
    (pv : Nat → Nat → Gen.Memory.Provenance M) (addr vtAddr a t va vt : Nat)
    (ha : addr < 2 ^ 64) (hv : vtAddr < 2 ^ 64) :
    Interp.encodeWidePtrM (M := M) (.VTablePointer tr)
      { thin_pointer := { addr := (addr : Int), provenance := some (pv a t) },
        metadata := some (.VTablePointer { addr := (vtAddr : Int), provenance := some (pv va vt) }) } =
      .ok (projBytes pv (encodePtrBytes addr 8 a t ++ encodePtrBytes vtAddr 8 va vt)) := by
  rw [encodeWidePtrM_dyn_eq tr addr vtAddr (some (pv a t)) (some (pv va vt)) ha hv]
  unfold projBytes
  rw [List.map_append]
  change Except.ok _ = Except.ok (projBytes pv (encodePtrBytes addr 8 a t) ++
    projBytes pv (encodePtrBytes vtAddr 8 va vt))
  rw [proj_encodePtrBytes (M := M) pv addr 8 a t, proj_encodePtrBytes (M := M) pv vtAddr 8 va vt]

/-- **Universal wide slice/`str` decode correspondence.** On any 8-byte coherent data half `d` and
8-byte initialized provenance-free metadata half `m`, `Trusted` (`decodePtrBytesNoForge` for both
`.slice elem` and `.str`) and MiniRust (`Interp.decodeWidePtrM .ElementCount`) decode identically. -/
theorem coherent_wide_slice_decode_agreement {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (isRef : Bool) (elem : RigidTy)
    (d m : List AbstractByte) (f : PtrByteFrag) (md : List UInt8)
    (hd : d.length = 8) (hm : m.length = 8)
    (hcoh : abstractBytesCoherentPtrProv? d = some f) (hw : f.ptrBytes = 8)
    (hmd : trData m = some md) (hplain : abstractBytesHaveProv m = false) :
    ∃ dd, trData d = some dd ∧
      decodePtrBytesNoForge isRef (.slice elem) 8 (d ++ m) =
        some (.aggregate 0 [.ptr { allocId := f.allocId, offsetBytes := Interp.leValue dd } 8,
          .scalar ⟨Interp.leValue md, 8⟩]) ∧
      decodePtrBytesNoForge isRef .str 8 (d ++ m) =
        some (.aggregate 0 [.ptr { allocId := f.allocId, offsetBytes := Interp.leValue dd } 8,
          .scalar ⟨Interp.leValue md, 8⟩]) ∧
      Interp.decodeWidePtrM (M := M) .ElementCount (projBytes pv (d ++ m)) =
        .ok (some (.Ptr {
          thin_pointer := { addr := ((Interp.leValue dd : Nat) : Int),
                            provenance := some (pv f.allocId f.tag) },
          metadata := some (.ElementCount ((Interp.leValue md : Nat) : Int)) })) := by
  obtain ⟨dd, hdd, hthin, _⟩ := coherent_decode_agreement (M := M) pv d f isRef hd hcoh hw
  have hmbits : decodeLittleEndianBits m = some (Interp.leValue md) := by
    rw [bits_eq_leValue, hmd]; rfl
  have hmeta : sliceMetaDecode 8 m = some (.scalar ⟨Interp.leValue md, 8⟩) := by
    unfold sliceMetaDecode; rw [hmbits, hplain]
  have hproj : projBytes pv (d ++ m) = projBytes pv d ++ projBytes pv m := List.map_append
  refine ⟨dd, hdd, ?_, ?_, ?_⟩
  · have h := decodePtrBytesNoForge_slice isRef elem d m (by omega) (by omega)
    rw [hd] at h; rw [h, hthin, hmeta]
  · have h := decodePtrBytesNoForge_str isRef d m (by omega) (by omega)
    rw [hd] at h; rw [h, hthin, hmeta]
  · rw [hproj, decodeWidePtrM_slice_eq _ _ (by rw [projBytes_length, hd]) (by rw [projBytes_length, hm]),
      proj_data, proj_data, hdd, hmd, trusted_coherent_implies_minirust_retains pv d f hcoh]

/-- **Universal wide `&dyn Trait` decode correspondence.** On any 8-byte coherent data half `d` and
8-byte coherent vtable half `m`, `Trusted` (`decodePtrBytesNoForge`) and MiniRust
(`Interp.decodeWidePtrM (.VTablePointer trId)`) decode identically. -/
theorem coherent_wide_dyn_decode_agreement {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (isRef : Bool) (tr : String) (trId : Gen.TraitName)
    (d m : List AbstractByte) (fd fm : PtrByteFrag)
    (hd : d.length = 8) (hm : m.length = 8)
    (hcd : abstractBytesCoherentPtrProv? d = some fd) (hwd : fd.ptrBytes = 8)
    (hcm : abstractBytesCoherentPtrProv? m = some fm) (hwm : fm.ptrBytes = 8) :
    ∃ dd md, trData d = some dd ∧ trData m = some md ∧
      decodePtrBytesNoForge isRef (.dynamic tr) 8 (d ++ m) =
        some (.aggregate 0 [.ptr { allocId := fd.allocId, offsetBytes := Interp.leValue dd } 8,
          .ptr { allocId := fm.allocId, offsetBytes := Interp.leValue md } 8]) ∧
      Interp.decodeWidePtrM (M := M) (.VTablePointer trId) (projBytes pv (d ++ m)) =
        .ok (some (.Ptr {
          thin_pointer := { addr := ((Interp.leValue dd : Nat) : Int),
                            provenance := some (pv fd.allocId fd.tag) },
          metadata := some (.VTablePointer {
            addr := ((Interp.leValue md : Nat) : Int),
            provenance := some (pv fm.allocId fm.tag) }) })) := by
  obtain ⟨dd, hdd, htd, _⟩ := coherent_decode_agreement (M := M) pv d fd isRef hd hcd hwd
  obtain ⟨md, hmd, htm, _⟩ := coherent_decode_agreement (M := M) pv m fm isRef hm hcm hwm
  have hproj : projBytes pv (d ++ m) = projBytes pv d ++ projBytes pv m := List.map_append
  refine ⟨dd, md, hdd, hmd, ?_, ?_⟩
  · have h := decodePtrBytesNoForge_dyn isRef tr d m (by omega) (by omega)
    rw [hd] at h; rw [h, htd, htm]
  · rw [hproj, decodeWidePtrM_dyn_eq trId _ _ (by rw [projBytes_length, hd]) (by rw [projBytes_length, hm]),
      proj_data, proj_data, hdd, hmd,
      trusted_coherent_implies_minirust_retains pv d fd hcd,
      trusted_coherent_implies_minirust_retains pv m fm hcm]

/-- **Universal swapped wide-slice divergence (`DIV-MR-PTR2INT`).** On `m ++ d` where `m` is an
8-byte plain integer and `d` is an 8-byte coherent pointer, `Trusted` rejects `m ++ d` under
`Ptr2IntTransmutePolicy.strictUcg630Ub` (`= none`), whereas MiniRust `decodeWidePtrM .ElementCount`
accepts it as a provenance-free data pointer with element count equal to `d`'s address. -/
theorem swapped_wide_slice_div {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (isRef : Bool) (elem : RigidTy)
    (m d : List AbstractByte) (f : PtrByteFrag) (md : List UInt8)
    (hm : m.length = 8) (hd : d.length = 8)
    (hmd : trData m = some md) (hm0 : ∃ v, m[0]? = some (.init v none))
    (hcd : abstractBytesCoherentPtrProv? d = some f) :
    ∃ dd, trData d = some dd ∧
      decodePtrBytesNoForge isRef (.slice elem) 8 (m ++ d) = none ∧
      Interp.decodeWidePtrM (M := M) .ElementCount (projBytes pv (m ++ d)) =
        .ok (some (.Ptr {
          thin_pointer := { addr := ((Interp.leValue md : Nat) : Int), provenance := none },
          metadata := some (.ElementCount ((Interp.leValue dd : Nat) : Int)) })) := by
  obtain ⟨_, _, hcoh⟩ := (coherent?_eq_some_iff d f).mp hcd
  obtain ⟨dd, hdd⟩ := trCoh_data _ _ _ _ d 0 hcoh
  have hdp : abstractBytesHaveProv d = true := by
    cases d with
    | nil => cases hd
    | cons x rest =>
      obtain ⟨v, rfl⟩ := hcoh.1
      rfl
  obtain ⟨v0, hv0⟩ := hm0
  have hmp : mrProvM M (projBytes pv m) = none := missing_provenance_strips_minirust pv m 0 v0 hv0
  have hproj : projBytes pv (m ++ d) = projBytes pv m ++ projBytes pv d := List.map_append
  refine ⟨dd, hdd, ?_, ?_⟩
  · have h := slice_meta_with_provenance_rejected isRef elem m d (by omega) (by omega) hdp
    rw [hm] at h; exact h
  · rw [hproj, decodeWidePtrM_slice_eq _ _ (by rw [projBytes_length, hm]) (by rw [projBytes_length, hd]),
      proj_data, proj_data, hmd, hdd, hmp]

/-! ### §9. `Kani#5205`: read-time validity of untyped bytes -/

/-- **MiniRust rejects every non-`0`/`1` byte at `Type::Bool`** (for any
fragment the byte may carry). -/
theorem minirust_bool_invalid (v : UInt8) (fr : Option (Gen.ProvenanceFrag Interp.Prov))
    (h0 : v ≠ 0) (h1 : v ≠ 1) :
    Interp.Type.decode .Bool [.Init v fr] = .ok none := by
  rw [Interp.Type.decode]
  · rfl
  · intro x h
    injection h with h _
    injection h with hv _
    exact h0 hv
  · intro x h
    injection h with h _
    injection h with hv _
    exact h1 hv

/-- **MiniRust accepts every initialized byte at `Type::Int(u8)`**: an invalid
`bool` bit pattern is representable as an untyped byte. -/
theorem minirust_u8_valid (v : UInt8) (fr : Option (Gen.ProvenanceFrag Interp.Prov)) :
    Interp.Type.decode (.Int ⟨.Unsigned, ⟨1⟩⟩) [.Init v fr] = .ok (some (.Int (v.toNat : Int))) := by
  rw [Interp.Type.decode]
  rfl

/-- **Universal polymorphic `Kani#5205` `Trusted` ↔ MiniRust `bool` validity correspondence**
across BOTH `BasicMemory` and `TreeBorrowsMemory` for every byte `v : UInt8`: untyped storage
accepts `v`, while typed `bool` decoding / validation agrees iff `v ∈ {0, 1}`. -/
theorem kani5205_bool_correspondence_M {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (layouts : LayoutTable) (tyBool : Ty)
    (hty : tyBool.kind = .bool) (v : UInt8) :
    decodeUntypedStorageBytes defaultCodecFuel layouts tyBool [.init v none] =
      some (.scalar ⟨v.toNat, 1⟩) ∧
    ((decodeTypedValueFromBytes defaultCodecFuel layouts tyBool [.init v none]).isSome = true ↔
      ∃ b, Interp.Type.decodeM (M := M) .Bool (projBytes pv [.init v none]) = .ok (some (.Bool b))) ∧
    (validateValueForTy? layouts (some tyBool) (.scalar ⟨v.toNat, 1⟩) = true ↔
      ∃ b, Interp.Type.decodeM (M := M) .Bool (projBytes pv [.init v none]) = .ok (some (.Bool b))) := by
  obtain ⟨kind, lidx⟩ := tyBool
  dsimp only at hty
  subst hty
  have hun : decodeUntypedStorageBytes defaultCodecFuel layouts ⟨.bool, lidx⟩ [.init v none] =
      some (.scalar ⟨v.toNat, 1⟩) := by
    show some (Value.scalar ⟨v.toBitVec.toNat + 256 * 0, 1⟩) = some (Value.scalar ⟨v.toNat, 1⟩)
    rw [Nat.mul_zero, Nat.add_zero]; rfl
  have hmr : Interp.Type.decodeM (M := M) .Bool (projBytes pv [.init v none]) =
      (if v = 0 then .ok (some (.Bool false))
       else if v = 1 then .ok (some (.Bool true))
       else .ok none) := minirust_bool_decodeM_iff (M := M) v none
  refine ⟨hun, ?_, ?_⟩
  · by_cases h0 : v = 0
    · subst h0
      have htr : decodeTypedValueFromBytes defaultCodecFuel layouts ⟨.bool, lidx⟩ [.init 0 none] =
          some (.scalar ⟨0, 1⟩) := rfl
      simp [hmr, htr]
    · by_cases h1 : v = 1
      · subst h1
        have htr : decodeTypedValueFromBytes defaultCodecFuel layouts ⟨.bool, lidx⟩ [.init 1 none] =
            some (.scalar ⟨1, 1⟩) := rfl
        simp [hmr, htr]
      · have hne0 : Nat.beq v.toBitVec.toNat 0 = false := by
          cases h : Nat.beq v.toBitVec.toNat 0 with
          | false => rfl
          | true =>
            have hv0 : v.toNat = 0 := (nat_beq_iff _ _).mp h
            exact absurd (UInt8.toNat_inj.mp hv0) h0
        have hne1 : Nat.beq v.toBitVec.toNat 1 = false := by
          cases h : Nat.beq v.toBitVec.toNat 1 with
          | false => rfl
          | true =>
            have hv1 : v.toNat = 1 := (nat_beq_iff _ _).mp h
            exact absurd (UInt8.toNat_inj.mp hv1) h1
        have htr : decodeTypedValueFromBytes defaultCodecFuel layouts ⟨.bool, lidx⟩ [.init v none] = none := by
          show (match Nat.beq v.toBitVec.toNat 0 with
            | true => some (Value.scalar ⟨0, 1⟩)
            | false => match Nat.beq v.toBitVec.toNat 1 with
              | true => some (Value.scalar ⟨1, 1⟩)
              | false => none) = none
          rw [hne0, hne1]
        simp [hmr, h0, h1, htr]
  · by_cases h0 : v = 0
    · subst h0
      have hval : validateValueForTy? layouts (some ⟨.bool, lidx⟩) (.scalar ⟨0, 1⟩) = true := rfl
      simp [hmr, hval]
    · by_cases h1 : v = 1
      · subst h1
        have hval : validateValueForTy? layouts (some ⟨.bool, lidx⟩) (.scalar ⟨1, 1⟩) = true := rfl
        simp [hmr, hval]
      · have hble : Nat.ble v.toNat 1 = false := by
          cases h : Nat.ble v.toNat 1 with
          | false => rfl
          | true =>
            have hle : v.toNat ≤ 1 := Nat.ble_eq.mp h
            have : v.toNat = 0 ∨ v.toNat = 1 := by omega
            rcases this with hv | hv
            · exact absurd (UInt8.toNat_inj.mp hv) h0
            · exact absurd (UInt8.toNat_inj.mp hv) h1
        have hval : validateValueForTy? layouts (some ⟨.bool, lidx⟩) (.scalar ⟨v.toNat, 1⟩) = false := by
          show Bool.and true (Nat.ble v.toNat 1) = false
          rw [hble]; rfl
        simp [hmr, h0, h1, hval]

/-! ### §10. Fixtures and kernel-checked witnesses -/

section Witnesses

open Trusted.Rustc.V2026_06_01.Layout

/-- `p = alloc 7 + 0x1000`. -/
def wP : List AbstractByte := encodePtrBytes 0x1000 8 7 7
/-- `p + 4`. -/
def wP4 : List AbstractByte := encodePtrBytes 0x1004 8 7 7
/-- `p + 256`: byte 0 is `0x00`, exactly as in `p`. -/
def wP256 : List AbstractByte := encodePtrBytes 0x1100 8 7 7
/-- The all-zero pointer image `alloc 7 + 0`. -/
def wZero : List AbstractByte := encodePtrBytes 0 8 7 7
/-- A pointer into another allocation. -/
def wOther : List AbstractByte := encodePtrBytes 0x1000 8 8 8
/-- The same allocation under another borrow tag. -/
def wOtherTag : List AbstractByte := encodePtrBytes 0x1000 8 7 9
/-- The plain integer `0x1000`. -/
def wPlain : List AbstractByte := encodePlainLittleEndianBytes 0x1000 8
/-- The plain slice length `3`. -/
def wLen3 : List AbstractByte := encodePlainLittleEndianBytes 3 8
/-- A vtable pointer `alloc 42 + 0x80`. -/
def wVt : List AbstractByte := encodePtrBytes 0x80 8 42 42

def wUnitL : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }
def wU8L : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wBoolL : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wCharL : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wU32L : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [wUnitL, wU8L, wBoolL, wCharL, wU32L] }
def wTyU8 : Ty := { kind := .uint .u8, layoutIdx := 1 }
def wTyBool : Ty := { kind := .bool, layoutIdx := 2 }
def wTyChar : Ty := { kind := .char, layoutIdx := 3 }
def wTyU32 : Ty := { kind := .uint .u32, layoutIdx := 4 }
/-- The little-endian bytes of the surrogate code point `0xD800`. -/
def wSurrogate : List AbstractByte :=
  [.init 0x00 none, .init 0xD8 none, .init 0x00 none, .init 0x00 none]

/-- **Round-trip witness (`alloc 7 + 0x1000`).** MiniRust `encode_ptr` produces
exactly the projected `Trusted` bytes, and both authorities decode them back to
the same pointer, across `BasicMemory` and `TreeBorrowsMemory`. -/
theorem w_roundtrip :
    Interp.encodePtr (⟨0x1000, some (bmProv 7 7)⟩ : Interp.Ptr) = .ok (projBytes bmProv wP) ∧
    Interp.encodePtrM (M := Interp.TBM) ⟨0x1000, some (tbProv 7 7)⟩ =
      .ok (projBytes tbProv wP) ∧
    Interp.decodePtr (projBytes bmProv wP) = .ok (some ⟨0x1000, some (bmProv 7 7)⟩) ∧
    Interp.decodePtrM (M := Interp.BM) (projBytes bmProv wP) =
      .ok (some ⟨0x1000, some (bmProv 7 7)⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv wP) =
      .ok (some ⟨0x1000, some (tbProv 7 7)⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 wP = some (.ptr ⟨7, 0x1000⟩ 8) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 wP = some (.ptr ⟨7, 0x1000⟩ 8) ∧
    decodeScalarLayoutBytesNoForge (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩) wP =
      some (.ptr ⟨7, 0x1000⟩ 8) ∧
    encodeUntypedValueToBytes 1 (.ptr ⟨7, 0x1000⟩ 8) = some wP ∧
    decodeRawAbstractByteVals? (wP.map encodeRawAbstractByteVal) = some wP := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **`UCG#558` W1 witnesses.** Full reversal (of the all-zero image of offset
`0`, and of `p`), the byte-0/byte-1 swap, and byte 0 repeated 8×: `Trusted`
reads a raw pointer as a plain integer and rejects a reference; MiniRust reads a
pointer without provenance. -/
theorem w_ucg558_w1 :
    decodePtrBytesNoForge false (.uint .u8) 8 wZero.reverse = some (.scalar ⟨0, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 wZero.reverse = none ∧
    Interp.decodePtr (projBytes bmProv wZero.reverse) = .ok (some ⟨0, none⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv wZero.reverse) = .ok (some ⟨0, none⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 wP.reverse = some (.scalar ⟨0x10000000000000, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 wP.reverse = none ∧
    Interp.decodePtr (projBytes bmProv wP.reverse) = .ok (some ⟨0x10000000000000, none⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 (swap01 wP) = some (.scalar ⟨0x10, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 (swap01 wP) = none ∧
    Interp.decodePtr (projBytes bmProv (swap01 wP)) = .ok (some ⟨0x10, none⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (swap01 wP)) = .ok (some ⟨0x10, none⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 (dupHead wP) = some (.scalar ⟨0, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 (dupHead wP) = none ∧
    Interp.decodePtr (projBytes bmProv (dupHead wP)) = .ok (some ⟨0, none⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (dupHead wP)) = .ok (some ⟨0, none⟩) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **Mixed / missing provenance and uninitialized bytes.** A cross-allocation
splice, one provenance byte followed by seven plain bytes, an all-plain integer
image (no integer-to-pointer forging), and a stream with one `.uninit` byte. -/
theorem w_mixed_missing_uninit :
    decodePtrBytesNoForge false (.uint .u8) 8 (wP.take 4 ++ wOther.drop 4) =
      some (.scalar ⟨0x1000, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 (wP.take 4 ++ wOther.drop 4) = none ∧
    Interp.decodePtr (projBytes bmProv (wP.take 4 ++ wOther.drop 4)) =
      .ok (some ⟨0x1000, none⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (wP.take 4 ++ wOther.drop 4)) =
      .ok (some ⟨0x1000, none⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 (wP.take 1 ++ wPlain.drop 1) =
      some (.scalar ⟨0x1000, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 (wP.take 1 ++ wPlain.drop 1) = none ∧
    Interp.decodePtr (projBytes bmProv (wP.take 1 ++ wPlain.drop 1)) =
      .ok (some ⟨0x1000, none⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 wPlain = some (.scalar ⟨0x1000, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 wPlain = none ∧
    Interp.decodePtr (projBytes bmProv wPlain) = .ok (some ⟨0x1000, none⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv wPlain) = .ok (some ⟨0x1000, none⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 (wP.take 7 ++ [.uninit]) = none ∧
    decodePtrBytesNoForge true (.uint .u8) 8 (wP.take 7 ++ [.uninit]) = none ∧
    Interp.decodePtr (projBytes bmProv (wP.take 7 ++ [.uninit])) = .ok none ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (wP.take 7 ++ [.uninit])) = .ok none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **`DIV-MR-OFFSET-SPLICE`: the `p` / `p + 4` splice.** Vendored MiniRust
retains the provenance and reads the pointer `alloc 7 + 0x1000`; `Trusted`
strips it (a raw pointer becomes the integer `0x1000`, a reference is invalid). -/
theorem w_offset_splice_p_p4 :
    Interp.decodePtr (projBytes bmProv (wP.take 4 ++ wP4.drop 4)) =
      .ok (some ⟨0x1000, some (bmProv 7 7)⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (wP.take 4 ++ wP4.drop 4)) =
      .ok (some ⟨0x1000, some (tbProv 7 7)⟩) ∧
    Interp.decodePtrProvenance 0 (Interp.firstProvenance (projBytes bmProv (wP.take 4 ++ wP4.drop 4)))
      (projBytes bmProv (wP.take 4 ++ wP4.drop 4)) = some (bmProv 7 7) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 (wP.take 4 ++ wP4.drop 4) =
      some (.scalar ⟨0x1000, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 (wP.take 4 ++ wP4.drop 4) = none ∧
    decodePtrBytesNoForge true (.fnPtr [] (.tuple []) .safe .rust) 8 (wP.take 4 ++ wP4.drop 4) =
      none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **`DIV-MR-OFFSET-SPLICE`: the `p` / `p + 256` splice.** Byte 0 is `0x00` in
both pointers, so the spliced byte *values* are exactly those of `p + 256`;
only the fragment's originating offset tells the bytes apart. MiniRust retains
the provenance; `Trusted` strips it. -/
theorem w_offset_splice_p_p256 :
    wP[0]? = some (.init 0x00 (some ⟨7, 7, 0, 0x1000, 8⟩)) ∧
    wP256[0]? = some (.init 0x00 (some ⟨7, 7, 0, 0x1100, 8⟩)) ∧
    Interp.decodePtr (projBytes bmProv (wP.take 1 ++ wP256.drop 1)) =
      .ok (some ⟨0x1100, some (bmProv 7 7)⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (wP.take 1 ++ wP256.drop 1)) =
      .ok (some ⟨0x1100, some (tbProv 7 7)⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 (wP.take 1 ++ wP256.drop 1) =
      some (.scalar ⟨0x1100, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 (wP.take 1 ++ wP256.drop 1) = none ∧
    decodePtrBytesNoForge false (.uint .u8) 8 wP256 = some (.ptr ⟨7, 0x1100⟩ 8) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **`DIV-MR-BASIC-TAG`.** A splice of two pointers into one allocation under
different borrow tags: `Trusted` and `TreeBorrowsMemory` strip the provenance,
while tag-blind `BasicMemory` retains it. -/
theorem w_basic_memory_tag_blind :
    decodePtrBytesNoForge false (.uint .u8) 8 (wP.take 4 ++ wOtherTag.drop 4) =
      some (.scalar ⟨0x1000, 8⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (wP.take 4 ++ wOtherTag.drop 4)) =
      .ok (some ⟨0x1000, none⟩) ∧
    Interp.decodePtr (projBytes bmProv (wP.take 4 ++ wOtherTag.drop 4)) =
      .ok (some ⟨0x1000, some (bmProv 7 7)⟩) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **Wide slice pointers** (`&[u8]`, `*const [u8]`, `&str`): the intact
`data ++ len` image decodes identically in both authorities. -/
theorem w_wide_slice :
    decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (wP ++ wLen3) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨3, 8⟩]) ∧
    decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (wP ++ wLen3) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨3, 8⟩]) ∧
    decodePtrBytesNoForge true .str 8 (wP ++ wLen3) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨3, 8⟩]) ∧
    Interp.decodeWidePtr .ElementCount (projBytes bmProv (wP ++ wLen3)) =
      .ok (some (.Ptr ⟨⟨0x1000, some (bmProv 7 7)⟩, some (.ElementCount 3)⟩)) ∧
    Interp.decodeWidePtrM (M := Interp.TBM) .ElementCount (projBytes tbProv (wP ++ wLen3)) =
      .ok (some (.Ptr ⟨⟨0x1000, some (tbProv 7 7)⟩, some (.ElementCount 3)⟩)) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **Swapped halves (`DIV-MR-PTR2INT`).** For `len ++ data`, `Trusted` rejects
the provenance-bearing length half (for `&[u8]`, `*const [u8]`, and `&str`);
MiniRust decodes the "length" at `Type::Int`, which ignores provenance, and
yields a provenance-free data pointer `3` with element count `0x1000`. A
reversed data half is stripped by both. -/
theorem w_wide_swapped_halves :
    decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (wLen3 ++ wP) = none ∧
    decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (wLen3 ++ wP) = none ∧
    decodePtrBytesNoForge true .str 8 (wLen3 ++ wP) = none ∧
    Interp.decodeWidePtr .ElementCount (projBytes bmProv (wLen3 ++ wP)) =
      .ok (some (.Ptr ⟨⟨3, none⟩, some (.ElementCount 0x1000)⟩)) ∧
    Interp.decodeWidePtrM (M := Interp.TBM) .ElementCount (projBytes tbProv (wLen3 ++ wP)) =
      .ok (some (.Ptr ⟨⟨3, none⟩, some (.ElementCount 0x1000)⟩)) ∧
    decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (wP.reverse ++ wLen3) = none ∧
    decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (wP.reverse ++ wLen3) =
      some (.aggregate 0 [.scalar ⟨0x10000000000000, 8⟩, .scalar ⟨3, 8⟩]) ∧
    Interp.decodeWidePtr .ElementCount (projBytes bmProv (wP.reverse ++ wLen3)) =
      .ok (some (.Ptr ⟨⟨0x10000000000000, none⟩, some (.ElementCount 3)⟩)) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **Trait-object pointers (`&dyn Trait`, `DIV-MR-DYN-VTABLE`).** The intact
`data ++ vtable` image decodes identically; with a reversed vtable half
`Trusted` rejects `&dyn Trait` at decode time (and reads `*const dyn Trait` as a
data pointer with an integer), while MiniRust decodes a provenance-free vtable
pointer that only `check_value` rejects. -/
theorem w_wide_dyn :
    decodePtrBytesNoForge true (.dynamic "T") 8 (wP ++ wVt) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .ptr ⟨42, 0x80⟩ 8]) ∧
    Interp.decodeWidePtr (.VTablePointer ⟨⟨0⟩⟩) (projBytes bmProv (wP ++ wVt)) =
      .ok (some (.Ptr ⟨⟨0x1000, some (bmProv 7 7)⟩,
        some (.VTablePointer ⟨0x80, some (bmProv 42 42)⟩)⟩)) ∧
    Interp.decodeWidePtrM (M := Interp.TBM) (.VTablePointer ⟨⟨0⟩⟩) (projBytes tbProv (wP ++ wVt)) =
      .ok (some (.Ptr ⟨⟨0x1000, some (tbProv 7 7)⟩,
        some (.VTablePointer ⟨0x80, some (tbProv 42 42)⟩)⟩)) ∧
    decodePtrBytesNoForge true (.dynamic "T") 8 (wP ++ wVt.reverse) = none ∧
    decodePtrBytesNoForge false (.dynamic "T") 8 (wP ++ wVt.reverse) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨0x8000000000000000, 8⟩]) ∧
    Interp.decodeWidePtr (.VTablePointer ⟨⟨0⟩⟩) (projBytes bmProv (wP ++ wVt.reverse)) =
      .ok (some (.Ptr ⟨⟨0x1000, some (bmProv 7 7)⟩,
        some (.VTablePointer ⟨0x8000000000000000, none⟩)⟩)) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **`Kani#5205`, `2u8` as `bool`.** The byte `2` is representable as an untyped
byte in both authorities (`u8`, the raw-byte carrier, MiniRust `Type::Int(u8)`
and `[u8; 1]`) — writing it is not UB — and is rejected by the typed `bool`
decode of both authorities (`Trusted`: `none`, the `.ub` read fault; MiniRust:
`None`). -/
theorem w_kani5205_bool :
    encodeUntypedValueToBytes 1 (.scalar ⟨2, 1⟩) = some [.init 2 none] ∧
    encodeValueToBytes defaultCodecFuel wLayouts wTyU8 (.scalar ⟨2, 1⟩) = some [.init 2 none] ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyU8 [.init 2 none] =
      some (.scalar ⟨2, 1⟩) ∧
    decodeRawAbstractByteVals? [encodeRawAbstractByteVal (.init 2 none)] = some [.init 2 none] ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyBool [.init 2 none] = none ∧
    validateValueForTy? wLayouts (some wTyBool) (.scalar ⟨2, 1⟩) = false ∧
    validateValueForTy? wLayouts (some wTyU8) (.scalar ⟨2, 1⟩) = true ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyBool [.init 1 none] =
      some (.scalar ⟨1, 1⟩) ∧
    Interp.Type.decode (.Int ⟨.Unsigned, ⟨1⟩⟩) (projBytes bmProv [.init 2 none]) =
      .ok (some (.Int 2)) ∧
    Interp.Type.decode .Bool (projBytes bmProv [.init 2 none]) = .ok none ∧
    Interp.Type.decode .Bool (projBytes bmProv [.init 1 none]) = .ok (some (.Bool true)) ∧
    Interp.Type.decodeM (M := Interp.TBM) (.Int ⟨.Unsigned, ⟨1⟩⟩) (projBytes tbProv [.init 2 none]) =
      .ok (some (.Int 2)) ∧
    Interp.Type.decodeM (M := Interp.TBM) .Bool (projBytes tbProv [.init 2 none]) = .ok none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **`Kani#5205`, `0xD800` as `char` (`DIV-MR-CHAR`).** The surrogate bit
pattern is representable as untyped bytes (`u32`, MiniRust `Type::Int(u32)`) and
is rejected by the `Trusted` typed `char` decode. MiniRust has no `char` type:
its closest type, `Type::Int(u32)`, accepts the pattern. -/
theorem w_kani5205_char :
    encodeUntypedValueToBytes 1 (.scalar ⟨0xD800, 4⟩) = some wSurrogate ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyU32 wSurrogate =
      some (.scalar ⟨0xD800, 4⟩) ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyChar wSurrogate = none ∧
    validateValueForTy? wLayouts (some wTyChar) (.scalar ⟨0xD800, 4⟩) = false ∧
    validateValueForTy? wLayouts (some wTyU32) (.scalar ⟨0xD800, 4⟩) = true ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyChar
      [.init 0x41 none, .init 0 none, .init 0 none, .init 0 none] = some (.scalar ⟨0x41, 4⟩) ∧
    Interp.Type.decode (.Int ⟨.Unsigned, ⟨4⟩⟩) (projBytes bmProv wSurrogate) =
      .ok (some (.Int 0xD800)) ∧
    Interp.Type.decodeM (M := Interp.TBM) (.Int ⟨.Unsigned, ⟨4⟩⟩) (projBytes tbProv wSurrogate) =
      .ok (some (.Int 0xD800)) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-! ### §11. Non-vacuous instantiations of the universal theorems -/

theorem coherent_decode_agreement_instance :
    (∃ data, trData wP = some data ∧
      thinDecode true 8 wP = some (.ptr { allocId := 7, offsetBytes := Interp.leValue data } 8) ∧
      Interp.decodePtrM (M := Interp.BM) (projBytes bmProv wP) =
        .ok (some { addr := ((Interp.leValue data : Nat) : Int),
                    provenance := some (bmProv 7 7) })) ∧
    (∃ data, trData wP = some data ∧
      thinDecode false 8 wP = some (.ptr { allocId := 7, offsetBytes := Interp.leValue data } 8) ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv wP) =
        .ok (some { addr := ((Interp.leValue data : Nat) : Int),
                    provenance := some (tbProv 7 7) })) :=
  ⟨coherent_decode_agreement (M := Interp.BM) bmProv wP ⟨7, 7, 0, 0x1000, 8⟩ true rfl rfl rfl,
   coherent_decode_agreement (M := Interp.TBM) tbProv wP ⟨7, 7, 0, 0x1000, 8⟩ false rfl rfl rfl⟩

theorem encode_roundtrip_instance :
    Interp.encodePtrM (M := Interp.TBM) { addr := ((0x1000 : Nat) : Int), provenance := some (tbProv 7 7) } =
      .ok (projBytes tbProv (encodePtrBytes 0x1000 8 7 7)) ∧
    Interp.encodePtr { addr := ((0x1000 : Nat) : Int), provenance := some (bmProv 7 7) } =
      .ok (projBytes bmProv (encodePtrBytes 0x1000 8 7 7)) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (encodePtrBytes 0x1000 8 7 7)) =
      .ok (some { addr := ((0x1000 : Nat) : Int), provenance := some (tbProv 7 7) }) ∧
    thinDecode true 8 (encodePtrBytes 0x1000 8 7 7) =
      some (.ptr { allocId := 7, offsetBytes := 0x1000 % 256 ^ 8 } 8) ∧
    thinDecode false 4 (encodePtrBytes 0x1000 4 9 9) =
      some (.ptr { allocId := 9, offsetBytes := 0x1000 % 256 ^ 4 } 4) :=
  ⟨encodePtrM_proj tbProv 0x1000 7 7 (by decide), encodePtr_proj 0x1000 7 7 (by decide),
   decodePtrM_proj_encodePtrBytes tbProv 0x1000 7 7 (by decide),
   thinDecode_encodePtrBytes true 0x1000 8 7 7 (by decide),
   thinDecode_encodePtrBytes false 0x1000 4 9 9 (by decide)⟩

theorem rawCarrier_ptr_roundtrip_instance :
    ∃ bs, decodeRawAbstractByteVals? (wP.map encodeRawAbstractByteVal) = some bs ∧
      thinDecode true 8 bs = some (.ptr { allocId := 7, offsetBytes := 0x1000 } 8) ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv bs) =
        .ok (some { addr := ((0x1000 : Nat) : Int), provenance := some (tbProv 7 7) }) :=
  rawCarrier_ptr_roundtrip (M := Interp.TBM) tbProv true 0x1000 7 7 (by decide)

theorem strip_laws_instance :
    (abstractBytesCoherentPtrProv? wZero.reverse = none ∧
      mrProvM Interp.BM (projBytes bmProv wZero.reverse) = none) ∧
    (abstractBytesCoherentPtrProv? (swap01 wP) = none ∧
      mrProvM Interp.TBM (projBytes tbProv (swap01 wP)) = none) ∧
    (abstractBytesCoherentPtrProv? (dupHead wP) = none ∧
      mrProvM Interp.TBM (projBytes tbProv (dupHead wP)) = none) ∧
    abstractBytesCoherentPtrProv? (wP.take 4 ++ wOther.drop 4) = none ∧
    mrProvM Interp.BM (projBytes bmProv (wP.take 4 ++ wOther.drop 4)) = none ∧
    abstractBytesCoherentPtrProv? wPlain = none ∧
    mrProvM Interp.TBM (projBytes tbProv wPlain) = none ∧
    thinDecode true 8 (wP.take 7 ++ [.uninit]) = none ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (wP.take 7 ++ [.uninit])) = .ok none :=
  ⟨reversal_strips bmProv 0 7 7, swap01_strips tbProv 0x1000 7 7, dupHead_strips tbProv 0x1000 7 7,
   mixed_provenance_strips_trusted _ 0 4 _ _ ⟨7, 7, 0, 0x1000, 8⟩ ⟨8, 8, 4, 0x1000, 8⟩ rfl rfl
     (Or.inl (by decide)),
   mixed_provenance_strips_minirust (M := Interp.BM) bmProv _ 0 4 _ _ ⟨7, 7, 0, 0x1000, 8⟩
     ⟨8, 8, 4, 0x1000, 8⟩ rfl rfl (by decide),
   missing_provenance_strips_trusted wPlain 0 _ rfl,
   missing_provenance_strips_minirust (M := Interp.TBM) tbProv wPlain 0 _ rfl,
   uninit_rejected_trusted true 8 _ (List.mem_append_right _ (List.Mem.head _)),
   uninit_rejected_minirust (M := Interp.TBM) tbProv _ rfl
     (List.mem_append_right _ (List.Mem.head _))⟩

/-- The `p` / `p + 4` and `p` / `p + 256` splices instantiate both halves of the
strict refinement, and `converse_gap_iff` on a non-degenerate stream. -/
theorem offset_splice_instance :
    abstractBytesCoherentPtrProv? (wP.take 4 ++ wP4.drop 4) = none ∧
    mrProvM Interp.TBM (projBytes tbProv (wP.take 4 ++ wP4.drop 4)) = some (tbProv 7 7) ∧
    abstractBytesCoherentPtrProv? (wP.take 1 ++ wP256.drop 1) = none ∧
    mrProvM Interp.BM (projBytes bmProv (wP.take 1 ++ wP256.drop 1)) = some (bmProv 7 7) ∧
    (abstractBytesCoherentPtrProv? (wP.take 1 ++ wP256.drop 1) = none ↔
      ∃ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
        (wP.take 1 ++ wP256.drop 1)[i]? = some (.init vi (some fi)) ∧
        (wP.take 1 ++ wP256.drop 1)[j]? = some (.init vj (some fj)) ∧
        (fi.origOffset ≠ fj.origOffset ∨ fi.ptrBytes ≠ fj.ptrBytes ∨
          fi.ptrBytes ≠ (wP.take 1 ++ wP256.drop 1).length)) :=
  ⟨offset_splice_trusted_strips _ 0x1000 0x1004 8 7 7 0 4 _ _ rfl rfl rfl rfl (by decide),
   offset_splice_minirust_retains (M := Interp.TBM) tbProv _ 0x1000 0x1004 8 7 7
     (List.cons_ne_nil _ _) (by
       intro i b h
       match i, h with
       | 0, h => exact Or.inl h
       | 1, h => exact Or.inl h
       | 2, h => exact Or.inl h
       | 3, h => exact Or.inl h
       | 4, h => exact Or.inr h
       | 5, h => exact Or.inr h
       | 6, h => exact Or.inr h
       | 7, h => exact Or.inr h
       | _ + 8, h =>
         have h' : (none : Option AbstractByte) = some b := h
         cases h'),
   offset_splice_trusted_strips _ 0x1000 0x1100 8 7 7 0 1 _ _ rfl rfl rfl rfl (by decide),
   offset_splice_minirust_retains (M := Interp.BM) bmProv _ 0x1000 0x1100 8 7 7
     (List.cons_ne_nil _ _) (by
       intro i b h
       match i, h with
       | 0, h => exact Or.inl h
       | 1, h => exact Or.inr h
       | 2, h => exact Or.inr h
       | 3, h => exact Or.inr h
       | 4, h => exact Or.inr h
       | 5, h => exact Or.inr h
       | 6, h => exact Or.inr h
       | 7, h => exact Or.inr h
       | _ + 8, h =>
         have h' : (none : Option AbstractByte) = some b := h
         cases h'),
   converse_gap_iff (M := Interp.TBM) tbProv tbProv_inj _ (tbProv 7 7) rfl⟩

theorem wide_and_bool_instance :
    decodePtrBytesNoForge true (.slice (.uint .u8)) wLen3.length (wLen3 ++ wP) = none ∧
    decodePtrBytesNoForge false (.slice (.uint .u8)) wP.length (wP ++ wLen3) =
      (match thinDecode false wP.length wP, sliceMetaDecode wP.length wLen3 with
       | some dv, some mv => some (.aggregate 0 [dv, mv])
       | _, _ => none) ∧
    Interp.Type.decode .Bool [.Init 2 none] = .ok none ∧
    Interp.Type.decode (.Int ⟨.Unsigned, ⟨1⟩⟩) [.Init 2 none] = .ok (some (.Int ((2 : UInt8).toNat : Int))) :=
  ⟨slice_meta_with_provenance_rejected true (.uint .u8) wLen3 wP (by decide) rfl rfl,
   decodePtrBytesNoForge_slice false (.uint .u8) wP wLen3 (by decide) rfl,
   minirust_bool_invalid 2 none (by decide) (by decide), minirust_u8_valid 2 none⟩

def wUnalignedBoolL : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .arbitrary [⟨0⟩] [0], variants := .single 0, isUninhabited := false,
    fieldLayouts := [2] }
def wMaybeUninitBoolL : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [2, 0] }
def wKaniLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [wUnitL, wU8L, wBoolL, wCharL, wU32L, wUnalignedBoolL, wMaybeUninitBoolL] }
def wTyUnalignedBool : Ty := { kind := .adt "Unaligned" [.bool], layoutIdx := 5 }
def wTyMaybeUninitBool : Ty := { kind := .adt "core::mem::MaybeUninit" [.bool], layoutIdx := 6 }
def wTyRawPtrU8 : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }

/-- **`Kani#5205`: `Unaligned<bool>` and `MaybeUninit<bool>`** across `Trusted` and MiniRust
(`BasicMemory` and `TreeBorrowsMemory`). Untyped storage accepts `2u8` (including inside
`MaybeUninit<bool>` and MiniRust `Type::Union`); typed `Unaligned<bool>` / `bool` reads reject it
in both authorities. -/
theorem w_kani5205_unaligned_and_maybeuninit :
    decodeUntypedStorageBytes defaultCodecFuel wKaniLayouts wTyUnalignedBool [.init 2 none] =
      some (.aggregate 0 [.scalar ⟨2, 1⟩]) ∧
    decodeTypedValueFromBytes defaultCodecFuel wKaniLayouts wTyUnalignedBool [.init 2 none] = none ∧
    decodeTypedValueFromBytes defaultCodecFuel wKaniLayouts wTyUnalignedBool [.init 1 none] =
      some (.aggregate 0 [.scalar ⟨1, 1⟩]) ∧
    (decodeTypedValueFromBytes defaultCodecFuel wKaniLayouts wTyMaybeUninitBool [.init 2 none]).isSome = true ∧
    Interp.Type.decodeM (M := Interp.BM) (.Union [] [(⟨0⟩, ⟨1⟩)] ⟨1⟩ ⟨1⟩) [.Init 2 none] =
      .ok (some (.Union [[.Init 2 none]])) ∧
    Interp.Type.decodeM (M := Interp.TBM) (.Union [] [(⟨0⟩, ⟨1⟩)] ⟨1⟩ ⟨1⟩) [.Init 2 none] =
      .ok (some (.Union [[.Init 2 none]])) ∧
    Interp.Type.decodeM (M := Interp.BM) .Bool [.Init 2 none] = .ok none ∧
    Interp.Type.decodeM (M := Interp.TBM) .Bool [.Init 2 none] = .ok none ∧
    Interp.Type.decodeM (M := Interp.TBM) .Bool [.Uninit] = .ok none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- Complete non-vacuous instantiations of every universal `A0` and `ep2-B1` theorem in this
dialect: `scalarLayoutPtr_{coherent,incoherent,union_coherent,union_incoherent}`,
`scalarLayoutNonPtr_strictUb_rejects_prov`, `decodePtrBytesNoForge_{thin,str,dyn}`,
`encodeUntyped_ptr`, `encodeValueToBytes_thinPtr`, `proj_plain_bytes`,
`trusted_retains_implies_minirust_retains`, `thinDecode_{raw_incoherent,ref_incoherent,uninit}`,
`w1_transforms_decode_strips`, `offset_splice_decode_divergence`, `encodeWidePtrM_{slice,dyn}_proj`,
`coherent_wide_{slice,dyn}_decode_agreement`, `swapped_wide_slice_div`,
`kani5205_bool_correspondence_M`, and shared `*_eq_M` / `bmProv_eq_iff` / `minirust_*_decodeM`. -/
theorem ep2_b1_mr_non_vacuity_instances :
    decodeScalarLayoutBytesNoForge (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩) wP .strictUcg630Ub 8 =
      some (.ptr { allocId := 7, offsetBytes := 0x1000 } 8) ∧
    decodeScalarLayoutBytesNoForge (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩) wPlain .strictUcg630Ub 8 =
      some (.scalar ⟨0x1000, 8⟩) ∧
    decodeScalarLayoutBytesNoForge (.union (.pointer 0)) (encodePtrBytes 0x1000 4 9 9) .strictUcg630Ub 4 =
      some (.ptr { allocId := 9, offsetBytes := 0x1000 } 4) ∧
    decodeScalarLayoutBytesNoForge (.union (.pointer 0)) (encodePlainLittleEndianBytes 0x1000 4) .strictUcg630Ub 4 =
      some (.scalar ⟨0x1000, 4⟩) ∧
    (decodeScalarLayoutBytesNoForge (.initialized (.int 64 false) ⟨0, 0xFFFFFFFFFFFFFFFF⟩) wP .strictUcg630Ub 8 = none ∧
     decodeScalarLayoutBytesNoForge (.union (.int 64 false)) wP .strictUcg630Ub 8 = none) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 wP = thinDecode true 8 wP ∧
    decodePtrBytesNoForge true .str 8 (wP ++ wLen3) =
      (match thinDecode true 8 wP, sliceMetaDecode 8 wLen3 with
       | some dv, some mv => some (.aggregate 0 [dv, mv]) | _, _ => none) ∧
    decodePtrBytesNoForge true (.dynamic "T") 8 (wP ++ wVt) =
      (match thinDecode true 8 wP, thinDecode true 8 wVt with
       | some dv, some mv => some (.aggregate 0 [dv, mv]) | _, _ => none) ∧
    encodeUntypedValueToBytes 1 (.ptr ⟨7, 0x1000⟩ 8) = some wP ∧
    encodeValueToBytes 1 wLayouts wTyRawPtrU8 (.ptr ⟨7, 0x1000⟩ 8) = some wP ∧
    projBytes tbProv wPlain = Interp.encodePtrBytesM (M := Interp.TBM) none 0 (Interp.leBytes 0x1000 8) ∧
    (mrProvM Interp.TBM (projBytes tbProv wP)).isSome = true ∧
    thinDecode false 8 wPlain = some (.scalar ⟨0x1000, 8⟩) ∧
    thinDecode true 8 wPlain = none ∧
    thinDecode false 8 (wP.take 7 ++ [.uninit]) = none ∧
    (bmProv 7 7 = bmProv 7 9 ↔ (7 : Nat) = 7) ∧
    Interp.decodePtr (projBytes bmProv wP) = Interp.decodePtrM (M := Interp.BM) (projBytes bmProv wP) ∧
    Interp.encodePtr ⟨0x1000, some (bmProv 7 7)⟩ = Interp.encodePtrM (M := Interp.BM) ⟨0x1000, some (bmProv 7 7)⟩ ∧
    Interp.decodePtrProvenance 0 (Interp.firstProvenance (projBytes bmProv wP)) (projBytes bmProv wP) =
      Interp.decodePtrProvenanceM (M := Interp.BM) 0 (Interp.firstProvenance (projBytes bmProv wP)) (projBytes bmProv wP) ∧
    (∃ d, trData wP.reverse = some d ∧ thinDecode false 8 wP.reverse = some (.scalar ⟨Interp.leValue d, 8⟩) ∧
      thinDecode true 8 wP.reverse = none ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv wP.reverse) =
        .ok (some { addr := ((Interp.leValue d : Nat) : Int), provenance := none })) ∧
    (∃ d, trData (wP.take 1 ++ wP256.drop 1) = some d ∧
      thinDecode false 8 (wP.take 1 ++ wP256.drop 1) = some (.scalar ⟨Interp.leValue d, 8⟩) ∧
      thinDecode true 8 (wP.take 1 ++ wP256.drop 1) = none ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (wP.take 1 ++ wP256.drop 1)) =
        .ok (some { addr := ((Interp.leValue d : Nat) : Int), provenance := some (tbProv 7 7) })) ∧
    Interp.encodeWidePtrM (M := Interp.TBM) .ElementCount
      { thin_pointer := { addr := ((0x1000 : Nat) : Int), provenance := some (tbProv 7 7) },
        metadata := some (.ElementCount ((3 : Nat) : Int)) } =
      .ok (projBytes tbProv (wP ++ wLen3)) ∧
    Interp.encodeWidePtrM (M := Interp.TBM) (.VTablePointer ⟨⟨0⟩⟩)
      { thin_pointer := { addr := ((0x1000 : Nat) : Int), provenance := some (tbProv 7 7) },
        metadata := some (.VTablePointer { addr := ((0x80 : Nat) : Int), provenance := some (tbProv 42 42) }) } =
      .ok (projBytes tbProv (wP ++ wVt)) ∧
    (∃ dd, trData wP = some dd ∧
      decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (wP ++ wLen3) =
        some (.aggregate 0 [.ptr { allocId := 7, offsetBytes := Interp.leValue dd } 8,
          .scalar ⟨Interp.leValue [3, 0, 0, 0, 0, 0, 0, 0], 8⟩]) ∧
      decodePtrBytesNoForge true .str 8 (wP ++ wLen3) =
        some (.aggregate 0 [.ptr { allocId := 7, offsetBytes := Interp.leValue dd } 8,
          .scalar ⟨Interp.leValue [3, 0, 0, 0, 0, 0, 0, 0], 8⟩]) ∧
      Interp.decodeWidePtrM (M := Interp.TBM) .ElementCount (projBytes tbProv (wP ++ wLen3)) =
        .ok (some (.Ptr {
          thin_pointer := { addr := ((Interp.leValue dd : Nat) : Int), provenance := some (tbProv 7 7) },
          metadata := some (.ElementCount ((Interp.leValue [3, 0, 0, 0, 0, 0, 0, 0] : Nat) : Int)) }))) ∧
    (∃ dd md, trData wP = some dd ∧ trData wVt = some md ∧
      decodePtrBytesNoForge true (.dynamic "T") 8 (wP ++ wVt) =
        some (.aggregate 0 [.ptr { allocId := 7, offsetBytes := Interp.leValue dd } 8,
          .ptr { allocId := 42, offsetBytes := Interp.leValue md } 8]) ∧
      Interp.decodeWidePtrM (M := Interp.TBM) (.VTablePointer ⟨⟨0⟩⟩) (projBytes tbProv (wP ++ wVt)) =
        .ok (some (.Ptr {
          thin_pointer := { addr := ((Interp.leValue dd : Nat) : Int), provenance := some (tbProv 7 7) },
          metadata := some (.VTablePointer {
            addr := ((Interp.leValue md : Nat) : Int), provenance := some (tbProv 42 42) }) }))) ∧
    (∃ dd, trData wP = some dd ∧
      decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (wLen3 ++ wP) = none ∧
      Interp.decodeWidePtrM (M := Interp.TBM) .ElementCount (projBytes tbProv (wLen3 ++ wP)) =
        .ok (some (.Ptr {
          thin_pointer := { addr := ((Interp.leValue [3, 0, 0, 0, 0, 0, 0, 0] : Nat) : Int), provenance := none },
          metadata := some (.ElementCount ((Interp.leValue dd : Nat) : Int)) }))) ∧
    (decodeUntypedStorageBytes defaultCodecFuel wLayouts wTyBool [.init 2 none] = some (.scalar ⟨2, 1⟩) ∧
     ((decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyBool [.init 2 none]).isSome = true ↔
       ∃ b, Interp.Type.decodeM (M := Interp.TBM) .Bool (projBytes tbProv [.init 2 none]) = .ok (some (.Bool b))) ∧
     (validateValueForTy? wLayouts (some wTyBool) (.scalar ⟨(2 : UInt8).toNat, 1⟩) = true ↔
       ∃ b, Interp.Type.decodeM (M := Interp.TBM) .Bool (projBytes tbProv [.init 2 none]) = .ok (some (.Bool b)))) :=
  ⟨scalarLayoutPtr_coherent 0 ⟨0, 0xFFFFFFFFFFFFFFFF⟩ wP 0x1000 ⟨7, 7, 0, 0x1000, 8⟩ .strictUcg630Ub rfl rfl rfl rfl,
   scalarLayoutPtr_incoherent 0 ⟨0, 0xFFFFFFFFFFFFFFFF⟩ wPlain 0x1000 .strictUcg630Ub rfl rfl rfl,
   scalarLayoutPtr_union_coherent 0 4 (encodePtrBytes 0x1000 4 9 9) 0x1000 ⟨9, 9, 0, 0x1000, 4⟩ .strictUcg630Ub (by decide) rfl rfl rfl rfl,
   scalarLayoutPtr_union_incoherent 0 4 (encodePlainLittleEndianBytes 0x1000 4) 0x1000 .strictUcg630Ub (by decide) rfl rfl rfl,
   scalarLayoutNonPtr_strictUb_rejects_prov 64 false ⟨0, 0xFFFFFFFFFFFFFFFF⟩ 8 wP rfl,
   decodePtrBytesNoForge_thin true (.uint .u8) 8 wP rfl,
   decodePtrBytesNoForge_str true wP wLen3 (by decide) rfl,
   decodePtrBytesNoForge_dyn true "T" wP wVt (by decide) rfl,
   encodeUntyped_ptr 0 ⟨7, 0x1000⟩ 8 (by decide),
   encodeValueToBytes_thinPtr 0 wLayouts wTyRawPtrU8 ⟨7, 0x1000⟩ 8 rfl (by decide) (Or.inl ⟨.not, .uint .u8, rfl, rfl⟩),
   proj_plain_bytes (M := Interp.TBM) tbProv 8 0x1000 0,
   trusted_retains_implies_minirust_retains (M := Interp.TBM) tbProv wP rfl,
   thinDecode_raw_incoherent 8 wPlain 0x1000 (by decide) rfl rfl rfl,
   thinDecode_ref_incoherent 8 wPlain rfl,
   thinDecode_uninit false 8 (wP.take 7 ++ [.uninit]) rfl,
   bmProv_eq_iff 7 7 7 9,
   decodePtr_eq_M (projBytes bmProv wP),
   encodePtr_eq_M ⟨0x1000, some (bmProv 7 7)⟩,
   decodePtrProvenance_eq_M (projBytes bmProv wP) 0 (Interp.firstProvenance (projBytes bmProv wP)),
   (w1_transforms_decode_strips (M := Interp.TBM) tbProv 0x1000 7 7).1,
   offset_splice_decode_divergence (M := Interp.TBM) tbProv (wP.take 1 ++ wP256.drop 1)
     0x1000 0x1100 7 7 0 1 _ _ rfl
     (by intro k b hk; match k, hk with
       | 0, h => exact Or.inl h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h => exact Or.inr h
       | _ + 8, h => cases h)
     rfl rfl rfl rfl (by decide),
   encodeWidePtrM_slice_proj (M := Interp.TBM) tbProv 0x1000 3 7 7 (by decide) (by decide),
   encodeWidePtrM_dyn_proj (M := Interp.TBM) ⟨⟨0⟩⟩ tbProv 0x1000 0x80 7 7 42 42 (by decide) (by decide),
   coherent_wide_slice_decode_agreement (M := Interp.TBM) tbProv true (.uint .u8) wP wLen3
     ⟨7, 7, 0, 0x1000, 8⟩ [3, 0, 0, 0, 0, 0, 0, 0] rfl rfl rfl rfl rfl rfl,
   coherent_wide_dyn_decode_agreement (M := Interp.TBM) tbProv true "T" ⟨⟨0⟩⟩ wP wVt
     ⟨7, 7, 0, 0x1000, 8⟩ ⟨42, 42, 0, 0x80, 8⟩ rfl rfl rfl rfl rfl rfl,
   swapped_wide_slice_div (M := Interp.TBM) tbProv true (.uint .u8) wLen3 wP
     ⟨7, 7, 0, 0x1000, 8⟩ [3, 0, 0, 0, 0, 0, 0, 0] rfl rfl rfl ⟨3, rfl⟩ rfl,
   kani5205_bool_correspondence_M (M := Interp.TBM) tbProv wLayouts wTyBool rfl 2⟩


/-- **Universal `DIV-MR-CHAR` (`Kani#5205`, `char`).** For every 32-bit pattern `c`, `Trusted`'s
typed `char` validity is exactly `isValidCharCode c` (rejecting every surrogate and every value
above `0x10FFFF`), the `Trusted` untyped encoding of `c` projects to MiniRust's own little-endian
encoding of `c`, and MiniRust's closest type `Type::Int(u32)` accepts that encoding for every `c`.
MiniRust has no `char` type, so the typed rejection is `Trusted`-only. -/
theorem kani5205_char_divergence (c : Nat) (hc : c < 2 ^ 32) :
    validateValueForTy? wLayouts (some wTyChar) (.scalar ⟨c, 4⟩) = isValidCharCode c ∧
    projBytes bmProv (encodePlainLittleEndianBytes c 4) =
      (Interp.leBytes c 4).map (fun b => Gen.AbstractByte.Init b none) ∧
    Interp.Type.decode (.Int ⟨.Unsigned, ⟨4⟩⟩) (projBytes bmProv (encodePlainLittleEndianBytes c 4)) =
      .ok (some (.Int c)) := by
  have hp : projBytes bmProv (encodePlainLittleEndianBytes c 4) =
      (Interp.leBytes c 4).map (fun b => Gen.AbstractByte.Init b none) :=
    (proj_plain_bytes (M := Interp.BM) bmProv 4 c 0).trans (encodePtrBytesM_none _ 0)
  refine ⟨?_, hp, ?_⟩
  · show Bool.and (Nat.beq 4 4) (isValidCharCode c) = isValidCharCode c
    rfl
  · rw [hp]
    exact minirust_u32_accepts_all c hc

theorem kani5205_char_divergence_instance :
    (validateValueForTy? wLayouts (some wTyChar) (.scalar ⟨0xD800, 4⟩) = isValidCharCode 0xD800 ∧
      projBytes bmProv (encodePlainLittleEndianBytes 0xD800 4) =
        (Interp.leBytes 0xD800 4).map (fun b => Gen.AbstractByte.Init b none) ∧
      Interp.Type.decode (.Int ⟨.Unsigned, ⟨4⟩⟩) (projBytes bmProv (encodePlainLittleEndianBytes 0xD800 4)) =
        .ok (some (.Int 0xD800))) ∧
    isValidCharCode 0xD800 = false ∧ isValidCharCode 0x41 = true :=
  ⟨kani5205_char_divergence 0xD800 (by decide), rfl, rfl⟩

/-- Decoding LE bits of `encodePlainLittleEndianBytes c n` yields `c % 256 ^ n`. -/
theorem decodeLittleEndianBits_encodePlain :
    ∀ (n c : Nat), decodeLittleEndianBits (encodePlainLittleEndianBytes c n) = some (c % 256 ^ n)
  | 0, c => by
      show some 0 = some (c % 256 ^ 0)
      rw [Nat.pow_zero, Nat.mod_one]
  | n + 1, c => by
      show (match decodeLittleEndianBits (encodePlainLittleEndianBytes (c / 256) n) with
        | some hi => some (Nat.add (UInt8.ofNat c).toBitVec.toNat (Nat.mul 256 hi))
        | none => none) = some (c % 256 ^ (n + 1))
      rw [decodeLittleEndianBits_encodePlain n (c / 256)]
      show some ((UInt8.ofNat c).toNat + 256 * (c / 256 % 256 ^ n)) = some (c % 256 ^ (n + 1))
      rw [u8_ofNat_toNat, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]

/-- **Universal `Kani#5205` `char` correspondence across BOTH `BasicMemory` and `TreeBorrowsMemory`
via MiniRust's `Type::Enum` + `Discriminator::Branch` encoding (`minirustCharType`).**
For every 32-bit pattern `c < 2^32`, any `layouts`, any `tyChar` with `tyChar.kind = .char`, and
any `M ∈ {BasicMemory, TreeBorrowsMemory}`:
1. Untyped byte storage (`decodeUntypedStorageBytes`) succeeds for EVERY `c` (including all 2048
   surrogates `0xD800..=0xDFFF` and `> 0x10FFFF`, matching MiniRust `Type::Int(u32)` / `Type::Union`).
2. `Trusted.validateValueForTy?` and `Trusted.decodeTypedValueFromBytes` accept `c` **iff**
   MiniRust `Type.decodeM (M := M) minirustCharType` accepts the projected bytes! -/
theorem kani5205_char_correspondence_M {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M)
    (layouts : LayoutTable) (tyChar : Ty) (hty : tyChar.kind = .char)
    (c : Nat) (hc : c < 2 ^ 32) :
    let bs := encodePlainLittleEndianBytes c 4
    decodeUntypedStorageBytes defaultCodecFuel layouts tyChar bs = some (.scalar ⟨c, 4⟩) ∧
    ((decodeTypedValueFromBytes defaultCodecFuel layouts tyChar bs).isSome = true ↔
      ∃ v, Interp.Type.decodeM (M := M) minirustCharType (projBytes pv bs) = .ok (some v)) ∧
    (validateValueForTy? layouts (some tyChar) (.scalar ⟨c, 4⟩) = true ↔
      ∃ v, Interp.Type.decodeM (M := M) minirustCharType (projBytes pv bs) = .ok (some v)) := by
  intro bs
  obtain ⟨kind, lidx⟩ := tyChar
  dsimp only at hty
  subst hty
  have hp : projBytes pv bs =
      (Interp.leBytes c 4).map (fun b => Gen.AbstractByte.Init b none) :=
    (proj_plain_bytes (M := M) pv 4 c 0).trans (encodePtrBytesM_none_eq_map _ 0)
  have hbits : decodeLittleEndianBits bs = some c := by
    have h := decodeLittleEndianBits_encodePlain 4 c
    rw [Nat.mod_eq_of_lt (by omega : c < 256 ^ 4)] at h
    exact h
  have hlen : length bs = 4 := rfl
  have hnoprov : abstractBytesHaveProv bs = false := rfl
  have hunt : decodeUntypedStorageBytes defaultCodecFuel layouts { kind := .char, layoutIdx := lidx } bs =
      some (.scalar ⟨c, 4⟩) := by
    show (match Nat.beq (length bs) 4, policyRejectsProv .strictUcg630Ub bs with
      | true, false => match decodeLittleEndianBits bs with
        | some bits => some (Value.scalar ⟨bits, 4⟩)
        | none => none
      | _, _ => none) = some (.scalar ⟨c, 4⟩)
    have hpol : policyRejectsProv .strictUcg630Ub bs = false := by
      unfold policyRejectsProv; exact hnoprov
    rw [hlen, hpol, hbits]
  have hsc : decodeScalarBytes bs false = some ({ bits := c, sizeBytes := 4 }, none) := by
    unfold decodeScalarBytes decodeLittleEndianBytes
    rw [hlen, hbits]
  have hvalid_iff : isValidCharCode c = true ↔ (c < 0xD800 ∨ (0xE000 ≤ c ∧ c ≤ 0x10FFFF)) := by
    unfold isValidCharCode
    constructor
    · intro h
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
      rcases h with h1 | ⟨h2, h3⟩
      · left
        cases hc1 : Nat.ble 55296 c with
        | true => rw [hc1] at h1; cases h1
        | false =>
          by_cases hlt : c < 55296
          · exact hlt
          · have : 55296 ≤ c := by omega
            have := Nat.ble_eq.mpr this
            rw [this] at hc1; cases hc1
      · right; rw [Nat.ble_eq] at h2 h3; exact ⟨h2, h3⟩
    · intro h
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
      rcases h with h1 | ⟨h2, h3⟩
      · left
        cases hc1 : Nat.ble 55296 c with
        | false => rfl
        | true => have := Nat.ble_eq.mp hc1; omega
      · right; exact ⟨Nat.ble_eq.mpr h2, Nat.ble_eq.mpr h3⟩
  have hdec : decodeTypedValueFromBytes defaultCodecFuel layouts { kind := .char, layoutIdx := lidx } bs =
      if isValidCharCode c then some (.scalar ⟨c, 4⟩) else none := by
    show (match abstractBytesHaveProv bs with
      | true => none
      | false =>
        match Nat.beq (length bs) 4 with
        | false => none
        | true =>
          match decodeScalarBytes bs false with
          | some (sv, _) =>
            match isValidCharCode sv.bits with
            | true => some (Value.scalar sv)
            | false => none
          | none => none) = _
    rw [hnoprov, hlen, hsc]
    dsimp only
    cases isValidCharCode c <;> rfl
  have hval : validateValueForTy? layouts (some { kind := .char, layoutIdx := lidx }) (.scalar ⟨c, 4⟩) =
      isValidCharCode c := by
    show Bool.and (Nat.beq 4 4) (isValidCharCode c) = isValidCharCode c
    rfl
  rw [hp, minirust_char_decodeM_iff (M := M) c hc, hdec, hval]
  refine ⟨hunt, ?_, hvalid_iff⟩
  cases h : isValidCharCode c with
  | true => simp [hvalid_iff.mp h]
  | false =>
    constructor
    · intro hf; cases hf
    · intro hok; exact absurd (hvalid_iff.mpr hok) (by rw [h]; decide)

/-- Non-vacuous boundary instantiations of `kani5205_char_correspondence_M` across `BM` and `TBM`
(valid ASCII `0x41`, BMP edge `0xD7FF`, surrogates `0xD800`/`0xDFFF`, post-surrogate `0xE000`,
max Unicode `0x10FFFF`, out-of-range `0x110000`, plus `.Uninit`). -/
theorem w_kani5205_char_enum_instance :
    Interp.Type.decodeM (M := Interp.BM) minirustCharType
        (projBytes bmProv (encodePlainLittleEndianBytes 0x41 4)) = .ok (some (.Variant 0 (.Int 0x41))) ∧
    Interp.Type.decodeM (M := Interp.TBM) minirustCharType
        (projBytes tbProv (encodePlainLittleEndianBytes 0xD7FF 4)) = .ok (some (.Variant 0 (.Int 0xD7FF))) ∧
    Interp.Type.decodeM (M := Interp.TBM) minirustCharType
        (projBytes tbProv (encodePlainLittleEndianBytes 0xD800 4)) = .ok none ∧
    Interp.Type.decodeM (M := Interp.BM) minirustCharType
        (projBytes bmProv (encodePlainLittleEndianBytes 0xDFFF 4)) = .ok none ∧
    Interp.Type.decodeM (M := Interp.TBM) minirustCharType
        (projBytes tbProv (encodePlainLittleEndianBytes 0xE000 4)) = .ok (some (.Variant 1 (.Int 0xE000))) ∧
    Interp.Type.decodeM (M := Interp.TBM) minirustCharType
        (projBytes tbProv (encodePlainLittleEndianBytes 0x10FFFF 4)) = .ok (some (.Variant 1 (.Int 0x10FFFF))) ∧
    Interp.Type.decodeM (M := Interp.TBM) minirustCharType
        (projBytes tbProv (encodePlainLittleEndianBytes 0x110000 4)) = .ok none ∧
    Interp.Type.decodeM (M := Interp.TBM) minirustCharType [.Uninit, .Init 0 none, .Init 0 none, .Init 0 none] = .ok none ∧
    (decodeUntypedStorageBytes defaultCodecFuel wLayouts wTyChar (encodePlainLittleEndianBytes 0xD800 4) =
        some (.scalar ⟨0xD800, 4⟩) ∧
      ((decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyChar (encodePlainLittleEndianBytes 0xD800 4)).isSome = true ↔
        ∃ v, Interp.Type.decodeM (M := Interp.TBM) minirustCharType
          (projBytes tbProv (encodePlainLittleEndianBytes 0xD800 4)) = .ok (some v)) ∧
      (validateValueForTy? wLayouts (some wTyChar) (.scalar ⟨0xD800, 4⟩) = true ↔
        ∃ v, Interp.Type.decodeM (M := Interp.TBM) minirustCharType
          (projBytes tbProv (encodePlainLittleEndianBytes 0xD800 4)) = .ok (some v))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, minirust_char_uninit_decodeM _ _ _,
    kani5205_char_correspondence_M (M := Interp.TBM) tbProv wLayouts wTyChar rfl 0xD800 (by decide)⟩
  · rw [(proj_plain_bytes (M := Interp.BM) bmProv 4 0x41 0).trans (encodePtrBytesM_none_eq_map _ 0)]
    exact minirust_char_decodeM_eq (M := Interp.BM) 0x41 (by decide)
  · rw [(proj_plain_bytes (M := Interp.TBM) tbProv 4 0xD7FF 0).trans (encodePtrBytesM_none_eq_map _ 0)]
    exact minirust_char_decodeM_eq (M := Interp.TBM) 0xD7FF (by decide)
  · rw [(proj_plain_bytes (M := Interp.TBM) tbProv 4 0xD800 0).trans (encodePtrBytesM_none_eq_map _ 0)]
    exact minirust_char_decodeM_eq (M := Interp.TBM) 0xD800 (by decide)
  · rw [(proj_plain_bytes (M := Interp.BM) bmProv 4 0xDFFF 0).trans (encodePtrBytesM_none_eq_map _ 0)]
    exact minirust_char_decodeM_eq (M := Interp.BM) 0xDFFF (by decide)
  · rw [(proj_plain_bytes (M := Interp.TBM) tbProv 4 0xE000 0).trans (encodePtrBytesM_none_eq_map _ 0)]
    exact minirust_char_decodeM_eq (M := Interp.TBM) 0xE000 (by decide)
  · rw [(proj_plain_bytes (M := Interp.TBM) tbProv 4 0x10FFFF 0).trans (encodePtrBytesM_none_eq_map _ 0)]
    exact minirust_char_decodeM_eq (M := Interp.TBM) 0x10FFFF (by decide)
  · rw [(proj_plain_bytes (M := Interp.TBM) tbProv 4 0x110000 0).trans (encodePtrBytesM_none_eq_map _ 0)]
    exact minirust_char_decodeM_eq (M := Interp.TBM) 0x110000 (by decide)

/-- Little-endian optional byte list for a `CapturedAllocation` (no uninit bytes). -/
def leOptBytes (u : Nat) : Nat → List (Option UInt8)
  | 0 => []
  | n + 1 => some (UInt8.ofNat u) :: leOptBytes (u / 256) n

/-- **Universal `body.globals` relocation correspondence (`Trusted` ↔ `MiniRustSpec.Interp`,
64-bit, BOTH `BasicMemory` and `TreeBorrowsMemory`).**
For any global `CapturedAllocation` holding an 8-byte pointer relocation `(0, targetPtr)` with LE
bytes of any `addr < 2^64`, `globalAllocSliceToAbstractBytes` equals `encodePtrBytes`, projects to
MiniRust `encodePtrM`, decodes identically in `Trusted.evalGlobalDerefRead` (raw `*const u8` &
`&u8`) and `MiniRustSpec.Interp.decodePtrM`, and faults with `.ub` on a typed `u64` dereference
read under `.strictUcg630Ub` (`W5`). -/
theorem globalAlloc_reloc_correspondence_M {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M)
    (gId : Nat) (al : Align) (mutbl : Mutability) (targetPtr : ProvenancePtr)
    (addr : Nat) (haddr : addr < 2 ^ 64) :
    let alloc : CapturedAllocation :=
      { allocId := gId, bytes := leOptBytes addr 8, relocations := [(0, targetPtr)],
        align := al, mutability := mutbl }
    let bs := encodePtrBytes addr 8 targetPtr.allocId targetPtr.tag
    globalAllocSliceToAbstractBytes alloc 0 8 8 = some bs ∧
    Interp.encodePtrM (M := M) ⟨(addr : Int), some (pv targetPtr.allocId targetPtr.tag)⟩ =
      .ok (projBytes pv bs) ∧
    Interp.decodePtrM (M := M) (projBytes pv bs) =
      .ok (some ⟨(addr : Int), some (pv targetPtr.allocId targetPtr.tag)⟩) ∧
    evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some wTyRawPtrU8) =
      .ok (.ptr { allocId := targetPtr.allocId, offsetBytes := addr } 8) [] ∧
    evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some { kind := .ref .not (.uint .u8), layoutIdx := 0 }) =
      .ok (.ptr { allocId := targetPtr.allocId, offsetBytes := addr } 8) [] ∧
    evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some { kind := .uint .u64, layoutIdx := 0 }) = .ub := by
  intro alloc bs
  have hbits8 :
      Nat.add (UInt8.ofNat addr).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256 / 256 / 256)).toBitVec.toNat
        (Nat.mul 256 0))))))))))))))) = addr := by
    have h := decodeLittleEndianBits_encodePlain 8 addr
    rw [Nat.mod_eq_of_lt (by omega : addr < 256 ^ 8)] at h
    injection h with h
  have horig : readGlobalRelocOrigOffset (leOptBytes addr 8) 0 8 targetPtr = normPtrByteOffset 8 addr := by
    unfold readGlobalRelocOrigOffset
    show (match some (Nat.add (UInt8.ofNat addr).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256 / 256 / 256)).toBitVec.toNat
        (Nat.mul 256 0)))))))))))))))) with
      | some bits => normPtrByteOffset 8 bits
      | none => normPtrByteOffset 8 targetPtr.offsetBytes) = normPtrByteOffset 8 addr
    rw [hbits8]
  have hslice : globalAllocSliceToAbstractBytes alloc 0 8 8 = some bs := by
    unfold globalAllocSliceToAbstractBytes
    dsimp only [alloc, bs, encodePtrBytes, encodePtrBytesAux]
    simp only [globalAllocBytesAux, leOptBytes, lookupRelocEntry, get?, Nat.ble, Nat.blt,
      Nat.add, Nat.sub, Bool.and, Bool.not]
    have horig' : readGlobalRelocOrigOffset
        [some (UInt8.ofNat addr), some (UInt8.ofNat (addr / 256)),
         some (UInt8.ofNat (addr / 256 / 256)), some (UInt8.ofNat (addr / 256 / 256 / 256)),
         some (UInt8.ofNat (addr / 256 / 256 / 256 / 256)),
         some (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256)),
         some (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256 / 256)),
         some (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256 / 256 / 256))] 0 8 targetPtr =
        normPtrByteOffset 8 addr := horig
    rw [horig']; rfl
  have henc := encodePtrM_proj (M := M) pv addr targetPtr.allocId targetPtr.tag haddr
  have hdecM := decodePtrM_proj_encodePtrBytes (M := M) pv addr targetPtr.allocId targetPtr.tag haddr
  have hthin : ∀ isRef, decodePtrBytesNoForge isRef (.uint .u8) 8 bs =
      some (.ptr { allocId := targetPtr.allocId, offsetBytes := addr } 8) := by
    intro isRef
    have h := (decodePtrBytesNoForge_thin isRef (.uint .u8) 8 bs rfl).trans
      (thinDecode_encodePtrBytes isRef addr 8 targetPtr.allocId targetPtr.tag (by decide))
    rw [Nat.mod_eq_of_lt (by omega : addr < 256 ^ 8)] at h
    exact h
  have hraw : evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some wTyRawPtrU8) =
      .ok (.ptr { allocId := targetPtr.allocId, offsetBytes := addr } 8) [] := by
    unfold evalGlobalDerefRead
    simp only [wLayouts, wTyRawPtrU8, layoutPointerBytes, intCastTargetBytes, hslice]
    change (match decodePtrBytesNoForge false (.uint .u8) 8 bs with
      | some decodedVal =>
        match readProjectedValue [] decodedVal [] with
        | .ok fieldVal => PlaceReadResult.ok fieldVal []
        | .ub => .ub | .unsupported => .unsupported
      | none => .ub) = _
    rw [hthin false]; rfl
  have href : evalGlobalDerefRead [] alloc 0 8 [] wLayouts
      (some { kind := .ref .not (.uint .u8), layoutIdx := 0 }) =
      .ok (.ptr { allocId := targetPtr.allocId, offsetBytes := addr } 8) [] := by
    unfold evalGlobalDerefRead
    simp only [wLayouts, layoutPointerBytes, intCastTargetBytes, hslice]
    change (match decodePtrBytesNoForge true (.uint .u8) 8 bs with
      | some decodedVal =>
        match readProjectedValue [] decodedVal [] with
        | .ok fieldVal => PlaceReadResult.ok fieldVal []
        | .ub => .ub | .unsupported => .unsupported
      | none => .ub) = _
    rw [hthin true]; rfl
  have hu64 : evalGlobalDerefRead [] alloc 0 8 [] wLayouts
      (some { kind := .uint .u64, layoutIdx := 0 }) = .ub := rfl
  exact ⟨hslice, henc, hdecM, hraw, href, hu64⟩

def wPtrL : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false, fieldLayouts := [] }
def wArr8U8L : TypeLayout :=
  { size := ⟨8⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .array ⟨1⟩ 8, variants := .single 0, isUninhabited := false, fieldLayouts := [1] }
def wCopyLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [wUnitL, wU8L, wBoolL, wCharL, wU32L, wPtrL, wArr8U8L] }
def wTyRawPtrC : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 5 }
def wTyRefC : Ty := { kind := .ref .not (.uint .u8), layoutIdx := 5 }
def wTyArr8U8C : Ty := { kind := .array (.uint .u8) 8, layoutIdx := 6 }
def wCopyMem : Memory :=
  { emptyMemory with
    borrows := [
      { tag := 10, targetLocal := 0, targetProjection := [], perm := .frozen, rangeOffset := 0, rangeLen := 8 },
      { tag := 11, targetLocal := 1, targetProjection := [], perm := .active, rangeOffset := 0, rangeLen := 8 }
    ] }
def wCopyStep (srcTy dstTy : Ty) (srcSlot dstSlot : LocalSlot) (sOff dOff n : Nat) :
    Option LocalSlot :=
  let decls : List LocalDecl := [
    { mutability := .not, ty := srcTy, debugName := none },
    { mutability := .mut, ty := dstTy, debugName := none }
  ]
  let l := [srcSlot, dstSlot]
  match evalCopyMemory { frame := { blockIdx := 0, stmtIdx := 0, locals := l }, memory := wCopyMem }
      l decls wCopyLayouts ⟨10, sOff⟩ ⟨11, dOff⟩ n with
  | .ok (_ :: dst' :: _, _) => some dst'
  | _ => none
def wCopyRead (srcTy dstTy : Ty) (srcSlot dstSlot : LocalSlot) (sOff dOff n : Nat) :
    Option (Option Value) :=
  let decls : List LocalDecl := [
    { mutability := .not, ty := srcTy, debugName := none },
    { mutability := .mut, ty := dstTy, debugName := none }
  ]
  let l := [srcSlot, dstSlot]
  match evalCopyMemory { frame := { blockIdx := 0, stmtIdx := 0, locals := l }, memory := wCopyMem }
      l decls wCopyLayouts ⟨10, sOff⟩ ⟨11, dOff⟩ n with
  | .ok (l', _) =>
    match evalOperand l' (.copy ⟨1, []⟩) [] [] wCopyLayouts [] decls with
    | .ok v _ => some (some v)
    | .ub => some none
    | .unsupported => none
  | _ => none

/-- **End-to-end `body.globals` misaligned relocation & `evalCopyMemory` correspondence witness
(`Trusted` ↔ `MiniRustSpec.Interp`).**
1. Misaligned `[p, p]` global relocation read at offset `4`: BOTH `Trusted.evalGlobalDerefRead`
   (raw -> `.scalar`, ref -> `.ub`) AND `MiniRust` `decodePtrM` strip provenance.
2. End-to-end `Trusted.evalCopyMemory`:
   - intact 8B copy retains `.ptr ⟨7, 0x1000⟩ 8` in `Trusted` and `some (tbProv 7 7)` in `MiniRust`;
   - 4+4 swapped halves strip provenance in BOTH `Trusted` and `MiniRust`;
   - 1+7 `p` / `p+256` splice via two `evalCopyMemory` calls strips in `Trusted` (raw -> `.scalar
     ⟨0x1100, 8⟩`, ref -> `.ub`) while `MiniRust` retains `some (tbProv 7 7)` (`DIV-MR-OFFSET-SPLICE`). -/
theorem w_mr_global_reloc_and_copyMemory :
    let p : ProvenancePtr := { allocId := 7, offsetBytes := 0x1000 }
    let p256 : ProvenancePtr := { allocId := 7, offsetBytes := 0x1100 }
    let adjAlloc : CapturedAllocation :=
      { allocId := 50, bytes := leOptBytes 0x1000 8 ++ leOptBytes 0x1000 8,
        relocations := [(0, p), (8, p)], align := ⟨8⟩, mutability := .not }
    (∃ misBytes, globalAllocSliceToAbstractBytes adjAlloc 4 8 8 = some misBytes ∧
      evalGlobalDerefRead [] adjAlloc 4 8 [] wLayouts (some wTyRawPtrU8) =
        .ok (.scalar ⟨0x100000000000, 8⟩) [] ∧
      evalGlobalDerefRead [] adjAlloc 4 8 [] wLayouts (some { kind := .ref .not (.uint .u8), layoutIdx := 0 }) = .ub ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv misBytes) = .ok (some ⟨0x100000000000, none⟩)) ∧
    (∃ vIntact bsIntact,
      wCopyRead wTyRawPtrC wTyRefC (.init (.ptr p 8)) .uninit 0 0 8 = some (some (.ptr ⟨7, 0x1000⟩ 8)) ∧
      wCopyStep wTyRawPtrC wTyArr8U8C (.init (.ptr p 8)) .uninit 0 0 8 = some (.init vIntact) ∧
      encodeUntypedValueToBytes defaultCodecFuel vIntact = some bsIntact ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv bsIntact) = .ok (some ⟨0x1000, some (tbProv 7 7)⟩)) ∧
    (∃ s1 vSwap bsSwap,
      wCopyStep wTyRawPtrC wTyArr8U8C (.init (.ptr p 8)) .uninit 0 4 4 = some s1 ∧
      wCopyStep wTyRawPtrC wTyArr8U8C (.init (.ptr p 8)) s1 4 0 4 = some (.init vSwap) ∧
      wCopyRead wTyArr8U8C wTyRawPtrC (.init vSwap) .uninit 0 0 8 = some (some (.scalar ⟨0x100000000000, 8⟩)) ∧
      wCopyRead wTyArr8U8C wTyRefC (.init vSwap) .uninit 0 0 8 = some none ∧
      encodeUntypedValueToBytes defaultCodecFuel vSwap = some bsSwap ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv bsSwap) = .ok (some ⟨0x100000000000, none⟩)) ∧
    (∃ s1 vSplice bsSplice,
      wCopyStep wTyRawPtrC wTyArr8U8C (.init (.ptr p 8)) .uninit 0 0 1 = some s1 ∧
      wCopyStep wTyRawPtrC wTyArr8U8C (.init (.ptr p256 8)) s1 1 1 7 = some (.init vSplice) ∧
      wCopyRead wTyArr8U8C wTyRawPtrC (.init vSplice) .uninit 0 0 8 = some (some (.scalar ⟨0x1100, 8⟩)) ∧
      wCopyRead wTyArr8U8C wTyRefC (.init vSplice) .uninit 0 0 8 = some none ∧
      encodeUntypedValueToBytes defaultCodecFuel vSplice = some bsSplice ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv bsSplice) = .ok (some ⟨0x1100, some (tbProv 7 7)⟩)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨_, rfl, rfl, rfl, rfl⟩
  · refine ⟨_, _, rfl, rfl, rfl, rfl⟩
  · refine ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Non-vacuous instantiations of `globalAlloc_reloc_correspondence_M` across both `BM` and `TBM`. -/
theorem ep2_b2_mr_non_vacuity_instances :
    let p : ProvenancePtr := { allocId := 7, offsetBytes := 0x1000 }
    let alloc : CapturedAllocation :=
      { allocId := 50, bytes := leOptBytes 0x1000 8, relocations := [(0, p)],
        align := ⟨8⟩, mutability := .not }
    (globalAllocSliceToAbstractBytes alloc 0 8 8 = some (encodePtrBytes 0x1000 8 7 7) ∧
      Interp.encodePtrM (M := Interp.TBM) ⟨0x1000, some (tbProv 7 7)⟩ =
        .ok (projBytes tbProv (encodePtrBytes 0x1000 8 7 7)) ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (encodePtrBytes 0x1000 8 7 7)) =
        .ok (some ⟨0x1000, some (tbProv 7 7)⟩) ∧
      evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some wTyRawPtrU8) = .ok (.ptr ⟨7, 0x1000⟩ 8) [] ∧
      evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some { kind := .ref .not (.uint .u8), layoutIdx := 0 }) =
        .ok (.ptr ⟨7, 0x1000⟩ 8) [] ∧
      evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some { kind := .uint .u64, layoutIdx := 0 }) = .ub) ∧
    (globalAllocSliceToAbstractBytes alloc 0 8 8 = some (encodePtrBytes 0x1000 8 7 7) ∧
      Interp.encodePtrM (M := Interp.BM) ⟨0x1000, some (bmProv 7 7)⟩ =
        .ok (projBytes bmProv (encodePtrBytes 0x1000 8 7 7)) ∧
      Interp.decodePtrM (M := Interp.BM) (projBytes bmProv (encodePtrBytes 0x1000 8 7 7)) =
        .ok (some ⟨0x1000, some (bmProv 7 7)⟩) ∧
      evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some wTyRawPtrU8) = .ok (.ptr ⟨7, 0x1000⟩ 8) [] ∧
      evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some { kind := .ref .not (.uint .u8), layoutIdx := 0 }) =
        .ok (.ptr ⟨7, 0x1000⟩ 8) [] ∧
      evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some { kind := .uint .u64, layoutIdx := 0 }) = .ub) :=
  ⟨globalAlloc_reloc_correspondence_M (M := Interp.TBM) tbProv 50 ⟨8⟩ .not { allocId := 7, offsetBytes := 0x1000 } 0x1000 (by decide),
   globalAlloc_reloc_correspondence_M (M := Interp.BM) bmProv 50 ⟨8⟩ .not { allocId := 7, offsetBytes := 0x1000 } 0x1000 (by decide)⟩

end Witnesses

end V06

/-! ## `V2026_08_01`: correspondence of `Trusted.Rustc.V2026_08_01.MirSemantics` with `MiniRustSpec.Interp` -/

namespace V08

open Trusted.Sequence
open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! ### §1. The fragment projection -/

/-- The exact fragment projection `PtrByteFrag → ProvenanceFrag { provenance, position := byteIdx }`.
It forgets `origOffset` and `ptrBytes`, which MiniRust fragments do not carry. -/
def projFrag {P : Type} (pv : Nat → Nat → P) (f : PtrByteFrag) : Gen.ProvenanceFrag P :=
  { provenance := pv f.allocId f.tag, position := (f.byteIdx : Int) }

/-- Projection of a `Trusted` abstract byte to a MiniRust `AbstractByte`. -/
def projByte {P : Type} (pv : Nat → Nat → P) : AbstractByte → Gen.AbstractByte P
  | .uninit => .Uninit
  | .init b none => .Init b none
  | .init b (some f) => .Init b (some (projFrag pv f))

/-- Projection of a `Trusted` byte stream to a MiniRust byte list. -/
def projBytes {P : Type} (pv : Nat → Nat → P) (bs : List AbstractByte) :
    List (Gen.AbstractByte P) :=
  bs.map (projByte pv)

theorem projBytes_length {P : Type} (pv : Nat → Nat → P) (bs : List AbstractByte) :
    (projBytes pv bs).length = bs.length :=
  List.length_map _

theorem projBytes_get {P : Type} (pv : Nat → Nat → P) (bs : List AbstractByte) (i : Nat)
    (b : AbstractByte) (h : bs[i]? = some b) :
    (projBytes pv bs)[i]? = some (projByte pv b) := by
  unfold projBytes
  rw [List.getElem?_map, h]
  rfl

theorem projByte_eq_init_some {P : Type} (pv : Nat → Nat → P) (b : AbstractByte) (v : UInt8)
    (fr : Gen.ProvenanceFrag P) (h : projByte pv b = .Init v (some fr)) :
    ∃ f, b = .init v (some f) ∧ projFrag pv f = fr := by
  cases b with
  | uninit =>
      have h' : (Gen.AbstractByte.Uninit : Gen.AbstractByte P) = .Init v (some fr) := h
      cases h'
  | init w pr =>
      cases pr with
      | none =>
          have h' : Gen.AbstractByte.Init w (none : Option (Gen.ProvenanceFrag P)) =
              .Init v (some fr) := h
          injection h' with _ h2
          cases h2
      | some f =>
          have h' : Gen.AbstractByte.Init w (some (projFrag pv f)) = .Init v (some fr) := h
          injection h' with h1 h2
          injection h2 with h2
          subst h1
          exact ⟨f, rfl, h2⟩

theorem frag_ext (f g : PtrByteFrag) (h1 : f.allocId = g.allocId) (h2 : f.tag = g.tag)
    (h3 : f.byteIdx = g.byteIdx) (h4 : f.origOffset = g.origOffset)
    (h5 : f.ptrBytes = g.ptrBytes) : f = g := by
  cases f
  cases g
  simp_all

/-! ### §2. Exact characterization of `Trusted` fragment coherence -/

/-- `Trusted` positional coherence: byte `i` of `bs` (the first one having index
`idx`) is `.init _ (some { allocId := a, tag := t, byteIdx := idx + i, origOffset := o,
ptrBytes := pb })`, and the stream ends exactly at index `pb`. -/
def TrCoh (a t o pb : Nat) : Nat → List AbstractByte → Prop
  | idx, [] => idx = pb
  | idx, b :: rest => (∃ v, b = .init v (some ⟨a, t, idx, o, pb⟩)) ∧ TrCoh a t o pb (idx + 1) rest

theorem coherentAux_iff (a t o pb : Nat) :
    ∀ (bs : List AbstractByte) (idx : Nat),
      abstractBytesCoherentPtrProvAux a t o pb idx bs = true ↔ TrCoh a t o pb idx bs
  | [], idx => nat_beq_iff idx pb
  | b :: rest, idx => by
      have ih := coherentAux_iff a t o pb rest (idx + 1)
      cases b with
      | uninit =>
          show false = true ↔ _
          constructor
          · intro h
            cases h
          · rintro ⟨⟨v, hv⟩, _⟩
            cases hv
      | init v frag =>
          cases frag with
          | none =>
              show false = true ↔ _
              constructor
              · intro h
                cases h
              · rintro ⟨⟨v', hv⟩, _⟩
                injection hv with _ h2
                cases h2
          | some f =>
              obtain ⟨fa, ft, fi, fo, fpb⟩ := f
              show (Bool.and (Bool.and (Nat.beq fa a) (Bool.and (Nat.beq ft t)
                    (Bool.and (Nat.beq fi idx) (Bool.and (Nat.beq fo o) (Nat.beq fpb pb)))))
                  (abstractBytesCoherentPtrProvAux a t o pb (idx + 1) rest)) = true ↔
                (∃ v', AbstractByte.init v (some ⟨fa, ft, fi, fo, fpb⟩) =
                    .init v' (some ⟨a, t, idx, o, pb⟩)) ∧ TrCoh a t o pb (idx + 1) rest
              simp only [Bool.and_eq_true, nat_beq_iff, ih]
              constructor
              · rintro ⟨⟨h1, h2, h3, h4, h5⟩, hr⟩
                subst h1 h2 h3 h4 h5
                exact ⟨⟨v, rfl⟩, hr⟩
              · rintro ⟨⟨v', hv⟩, hr⟩
                injection hv with _ e2
                injection e2 with e2
                injection e2 with e1 e2 e3 e4 e5
                exact ⟨⟨e1, e2, e3, e4, e5⟩, hr⟩

/-- The coherence guard of `abstractBytesCoherentPtrProv?` on a fragment-headed stream. -/
def cohCond (g : PtrByteFrag) (rest : List AbstractByte) : Bool :=
  Bool.and (Nat.blt 0 g.ptrBytes)
    (Bool.and (Nat.beq g.byteIdx 0)
      (abstractBytesCoherentPtrProvAux g.allocId g.tag g.origOffset g.ptrBytes 1 rest))

theorem coherent?_cons_iff (v : UInt8) (g f : PtrByteFrag) (rest : List AbstractByte) :
    abstractBytesCoherentPtrProv? (.init v (some g) :: rest) = some f ↔
      cohCond g rest = true ∧ g = f := by
  show (match cohCond g rest with
    | true => some g
    | false => none) = some f ↔ _
  cases cohCond g rest
  · constructor
    · intro h
      cases h
    · rintro ⟨h, _⟩
      cases h
  · constructor
    · intro h
      injection h with h
      exact ⟨rfl, h⟩
    · rintro ⟨_, h⟩
      exact congrArg some h

/-- **Exact characterization of `abstractBytesCoherentPtrProv?`.** -/
theorem coherent?_eq_some_iff (bs : List AbstractByte) (f : PtrByteFrag) :
    abstractBytesCoherentPtrProv? bs = some f ↔
      0 < f.ptrBytes ∧ f.byteIdx = 0 ∧
        TrCoh f.allocId f.tag f.origOffset f.ptrBytes 0 bs := by
  cases bs with
  | nil =>
      show (none : Option PtrByteFrag) = some f ↔ _
      constructor
      · intro h
        cases h
      · rintro ⟨h0, _, h⟩
        have h' : 0 = f.ptrBytes := h
        omega
  | cons b rest =>
      cases b with
      | uninit =>
          show (none : Option PtrByteFrag) = some f ↔ _
          constructor
          · intro h
            cases h
          · rintro ⟨_, _, ⟨v, hv⟩, _⟩
            cases hv
      | init v frag =>
          cases frag with
          | none =>
              show (none : Option PtrByteFrag) = some f ↔ _
              constructor
              · intro h
                cases h
              · rintro ⟨_, _, ⟨v', hv⟩, _⟩
                injection hv with _ h2
                cases h2
          | some g =>
              rw [coherent?_cons_iff]
              unfold cohCond
              simp only [Bool.and_eq_true, nat_beq_iff, Nat.blt_eq, coherentAux_iff]
              constructor
              · rintro ⟨⟨h0, hi, hr⟩, hgf⟩
                subst hgf
                refine ⟨h0, hi, And.intro ⟨v, ?_⟩ hr⟩
                exact congrArg (fun x => AbstractByte.init v (some x))
                  (frag_ext _ _ rfl rfl hi rfl rfl)
              · rintro ⟨h0, hi, ⟨v', hv⟩, hr⟩
                injection hv with _ e2
                injection e2 with e2
                have hgf : g = f := by
                  rw [e2]
                  exact frag_ext _ _ rfl rfl hi.symm rfl rfl
                subst hgf
                exact ⟨⟨h0, hi, hr⟩, rfl⟩

theorem trCoh_get (a t o pb : Nat) :
    ∀ (bs : List AbstractByte) (idx : Nat), TrCoh a t o pb idx bs →
      ∀ (i : Nat) (b : AbstractByte), bs[i]? = some b →
        ∃ v, b = AbstractByte.init v (some ⟨a, t, idx + i, o, pb⟩)
  | [], _, _ => by
      intro i b hb
      cases hb
  | x :: rest, idx, h => by
      intro i b hb
      cases i with
      | zero =>
          have hx : some x = some b := hb
          injection hx with hx
          subst hx
          exact h.1
      | succ j =>
          have hb' : rest[j]? = some b := hb
          have := trCoh_get a t o pb rest (idx + 1) h.2 j b hb'
          have e : idx + 1 + j = idx + (j + 1) := by omega
          rw [e] at this
          exact this

theorem trCoh_of_get (a t o pb : Nat) :
    ∀ (bs : List AbstractByte) (idx : Nat), idx + bs.length = pb →
      (∀ (i : Nat) (b : AbstractByte), bs[i]? = some b →
        ∃ v, b = AbstractByte.init v (some ⟨a, t, idx + i, o, pb⟩)) →
      TrCoh a t o pb idx bs
  | [], idx, hlen, _ => by
      show idx = pb
      simpa using hlen
  | x :: rest, idx, hlen, h => by
      refine And.intro (h 0 x rfl) (trCoh_of_get a t o pb rest (idx + 1) ?_ ?_)
      · simp only [List.length_cons] at hlen
        omega
      · intro j b hb
        have := h (j + 1) b hb
        have e : idx + (j + 1) = idx + 1 + j := by omega
        rw [e] at this
        exact this

theorem trCoh_length (a t o pb : Nat) :
    ∀ (bs : List AbstractByte) (idx : Nat), TrCoh a t o pb idx bs → idx + bs.length = pb
  | [], idx, h => by
      have h' : idx = pb := h
      simpa using h'
  | _ :: rest, idx, h => by
      have := trCoh_length a t o pb rest (idx + 1) h.2
      simp only [List.length_cons]
      omega

/-- `Trusted` strips provenance as soon as one byte is not the fragment of its
own position (wrong `byteIdx`, no fragment, or uninitialized). -/
theorem coherent?_none_of_bad_position (bs : List AbstractByte) (i : Nat) (b : AbstractByte)
    (hb : bs[i]? = some b) (hbad : ∀ v f, b = .init v (some f) → f.byteIdx ≠ i) :
    abstractBytesCoherentPtrProv? bs = none := by
  cases h : abstractBytesCoherentPtrProv? bs with
  | none => rfl
  | some f =>
      obtain ⟨_, _, hc⟩ := (coherent?_eq_some_iff bs f).mp h
      obtain ⟨v, hv⟩ := trCoh_get _ _ _ _ bs 0 hc i b hb
      have := hbad v _ hv
      rw [Nat.zero_add] at this
      exact absurd rfl this

/-- `Trusted` strips provenance when two fragments disagree on the allocation,
the tag, the originating offset, or the pointer width. -/
theorem coherent?_none_of_field_mismatch (bs : List AbstractByte) (i j : Nat) (vi vj : UInt8)
    (fi fj : PtrByteFrag)
    (hi : bs[i]? = some (.init vi (some fi))) (hj : bs[j]? = some (.init vj (some fj)))
    (hne : fi.allocId ≠ fj.allocId ∨ fi.tag ≠ fj.tag ∨ fi.origOffset ≠ fj.origOffset ∨
      fi.ptrBytes ≠ fj.ptrBytes) :
    abstractBytesCoherentPtrProv? bs = none := by
  cases h : abstractBytesCoherentPtrProv? bs with
  | none => rfl
  | some f =>
      obtain ⟨_, _, hc⟩ := (coherent?_eq_some_iff bs f).mp h
      obtain ⟨v1, h1⟩ := trCoh_get _ _ _ _ bs 0 hc i _ hi
      obtain ⟨v2, h2⟩ := trCoh_get _ _ _ _ bs 0 hc j _ hj
      injection h1 with _ h1
      injection h1 with h1
      injection h2 with _ h2
      injection h2 with h2
      subst h1
      subst h2
      rcases hne with h | h | h | h <;> exact absurd rfl h

/-! ### §3. `Trusted → MiniRust` soundness: coherent streams decode identically -/

theorem trCoh_proj {P : Type} (pv : Nat → Nat → P) (a t o pb : Nat) :
    ∀ (bs : List AbstractByte) (idx : Nat), TrCoh a t o pb idx bs →
      MrCoh (pv a t) idx (projBytes pv bs)
  | [], _, _ => trivial
  | x :: rest, idx, h => by
      obtain ⟨⟨v, hv⟩, hr⟩ := h
      subst hv
      exact And.intro ⟨v, rfl⟩ (trCoh_proj pv a t o pb rest (idx + 1) hr)

/-- **Directional refinement (`Trusted` retains ⟹ MiniRust retains).** Whenever
`Trusted` finds the stream coherent, MiniRust `decode_ptr` retains the projected
provenance. -/
theorem trusted_coherent_implies_minirust_retains {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte) (f : PtrByteFrag)
    (h : abstractBytesCoherentPtrProv? bs = some f) :
    mrProvM M (projBytes pv bs) = some (pv f.allocId f.tag) := by
  obtain ⟨h0, _, hc⟩ := (coherent?_eq_some_iff bs f).mp h
  refine (mrProvM_eq_some_iff _ _).mpr ⟨?_, trCoh_proj pv _ _ _ _ bs 0 hc⟩
  cases bs with
  | nil =>
      have h' : 0 = f.ptrBytes := hc
      omega
  | cons b rest => exact List.cons_ne_nil _ _

/-- The directional refinement as an implication between the two verdicts. -/
theorem trusted_retains_implies_minirust_retains {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte)
    (h : (abstractBytesCoherentPtrProv? bs).isSome = true) :
    (mrProvM M (projBytes pv bs)).isSome = true := by
  cases hc : abstractBytesCoherentPtrProv? bs with
  | none =>
      rw [hc] at h
      cases h
  | some f =>
      rw [trusted_coherent_implies_minirust_retains pv bs f hc]
      rfl

/-- The byte data of a `Trusted` stream (`none` if any byte is uninitialized). -/
def trData : List AbstractByte → Option (List UInt8)
  | [] => some []
  | .uninit :: _ => none
  | .init b _ :: rest => (trData rest).map (b :: ·)

theorem proj_data {P : Type} (pv : Nat → Nat → P) :
    ∀ bs : List AbstractByte,
      (projBytes pv bs).mapM Interp.AbstractByte.dataM = trData bs
  | [] => rfl
  | .uninit :: rest => by
      show List.mapM Interp.AbstractByte.dataM (Gen.AbstractByte.Uninit :: projBytes pv rest) = none
      rw [List.mapM_cons]
      rfl
  | .init b none :: rest => by
      show List.mapM Interp.AbstractByte.dataM (Gen.AbstractByte.Init b none :: projBytes pv rest) =
        (trData rest).map (b :: ·)
      rw [List.mapM_cons, proj_data pv rest]
      cases trData rest <;> rfl
  | .init b (some f) :: rest => by
      show List.mapM Interp.AbstractByte.dataM
          (Gen.AbstractByte.Init b (some (projFrag pv f)) :: projBytes pv rest) =
        (trData rest).map (b :: ·)
      rw [List.mapM_cons, proj_data pv rest]
      cases trData rest <;> rfl

theorem bits_eq_leValue :
    ∀ bs : List AbstractByte, decodeLittleEndianBits bs = (trData bs).map Interp.leValue
  | [] => rfl
  | .uninit :: _ => rfl
  | .init b fr :: rest => by
      show (match decodeLittleEndianBits rest with
        | some highBits => some (Nat.add b.toBitVec.toNat (Nat.mul 256 highBits))
        | none => none) = ((trData rest).map (b :: ·)).map Interp.leValue
      rw [bits_eq_leValue rest]
      cases trData rest <;> rfl

theorem trCoh_data (a t o pb : Nat) :
    ∀ (bs : List AbstractByte) (idx : Nat), TrCoh a t o pb idx bs → ∃ data, trData bs = some data
  | [], _, _ => ⟨[], rfl⟩
  | x :: rest, idx, h => by
      obtain ⟨⟨v, hv⟩, hr⟩ := h
      obtain ⟨data, hd⟩ := trCoh_data a t o pb rest (idx + 1) hr
      subst hv
      refine ⟨v :: data, ?_⟩
      show (trData rest).map (v :: ·) = some (v :: data)
      rw [hd]
      rfl

theorem trData_none_of_uninit :
    ∀ bs : List AbstractByte, AbstractByte.uninit ∈ bs → trData bs = none
  | [], h => by cases h
  | .uninit :: _, _ => rfl
  | .init b fr :: rest, h => by
      have hr : AbstractByte.uninit ∈ rest := by
        cases h with
        | tail _ h' => exact h'
      show (trData rest).map (b :: ·) = none
      rw [trData_none_of_uninit rest hr]
      rfl

/-- MiniRust `decode_ptr` on the projection of an 8-byte `Trusted` stream. -/
theorem decodePtrM_proj {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte) (hlen : bs.length = 8) :
    Interp.decodePtrM (M := M) (projBytes pv bs) =
      .ok ((trData bs).map (fun data =>
        { addr := ((Interp.leValue data : Nat) : Int),
          provenance := mrProvM M (projBytes pv bs) })) := by
  rw [decodePtrM_eq _ (by rw [projBytes_length]; exact hlen), proj_data]

/-! ### §4. The `Trusted` thin-pointer decoder -/

/-- The thin-pointer half of `decodePtrBytesNoForge` (its local `dataOf`). -/
def thinDecode (isRef : Bool) (ptrBytes : Nat) (dataBytes : List AbstractByte) : Option Value :=
  match Nat.blt 0 ptrBytes, Nat.beq (length dataBytes) ptrBytes,
      decodeLittleEndianBits dataBytes with
  | true, true, .some bits =>
    match abstractBytesCoherentPtrProv? dataBytes with
    | .some frag =>
      match Nat.beq frag.ptrBytes ptrBytes with
      | true => .some (.ptr { allocId := frag.allocId, offsetBytes := bits } ptrBytes)
      | false =>
        match isRef with
        | true => .none
        | false => .some (.scalar ⟨bits, ptrBytes⟩)
    | .none =>
      match isRef with
      | true => .none
      | false => .some (.scalar ⟨bits, ptrBytes⟩)
  | _, _, _ => .none

/-- Pointees of thin pointers (everything but slices, `str`, and trait objects). -/
def thinPointee : RigidTy → Bool
  | .slice _ => false
  | .str => false
  | .dynamic _ => false
  | _ => true

/-- On a thin pointee, `decodePtrBytesNoForge` is `thinDecode`. -/
theorem decodePtrBytesNoForge_thin (isRef : Bool) (pointee : RigidTy) (pb : Nat)
    (bs : List AbstractByte) (h : thinPointee pointee = true) :
    decodePtrBytesNoForge isRef pointee pb bs = thinDecode isRef pb bs := by
  cases pointee <;> first | rfl | cases h

theorem thinDecode_coherent (isRef : Bool) (pb : Nat) (bs : List AbstractByte) (bits : Nat)
    (f : PtrByteFrag) (h0 : 0 < pb) (hlen : bs.length = pb)
    (hbits : decodeLittleEndianBits bs = some bits)
    (h : abstractBytesCoherentPtrProv? bs = some f) (hw : f.ptrBytes = pb) :
    thinDecode isRef pb bs = some (.ptr { allocId := f.allocId, offsetBytes := bits } pb) := by
  have e1 : Nat.blt 0 pb = true := by
    rw [Nat.blt_eq]
    exact h0
  have e2 : Nat.beq (length bs) pb = true := (nat_beq_iff _ _).mpr hlen
  have e3 : Nat.beq f.ptrBytes pb = true := (nat_beq_iff _ _).mpr hw
  unfold thinDecode
  rw [e1, e2, hbits]
  simp only [h, e3]

/-- A raw pointer read from an incoherent stream is an integer: no provenance is forged. -/
theorem thinDecode_raw_incoherent (pb : Nat) (bs : List AbstractByte) (bits : Nat)
    (h0 : 0 < pb) (hlen : bs.length = pb) (hbits : decodeLittleEndianBits bs = some bits)
    (h : abstractBytesCoherentPtrProv? bs = none) :
    thinDecode false pb bs = some (.scalar ⟨bits, pb⟩) := by
  have e1 : Nat.blt 0 pb = true := by
    rw [Nat.blt_eq]
    exact h0
  have e2 : Nat.beq (length bs) pb = true := (nat_beq_iff _ _).mpr hlen
  unfold thinDecode
  rw [e1, e2, hbits]
  simp only [h]

/-- A reference / `fn` pointer read from an incoherent stream is invalid. -/
theorem thinDecode_ref_incoherent (pb : Nat) (bs : List AbstractByte)
    (h : abstractBytesCoherentPtrProv? bs = none) :
    thinDecode true pb bs = none := by
  unfold thinDecode
  cases Nat.blt 0 pb <;> cases Nat.beq (length bs) pb <;>
    cases decodeLittleEndianBits bs <;> simp only [h]

/-- Any uninitialized byte makes the pointer decode fail. -/
theorem thinDecode_uninit (isRef : Bool) (pb : Nat) (bs : List AbstractByte)
    (h : decodeLittleEndianBits bs = none) : thinDecode isRef pb bs = none := by
  unfold thinDecode
  rw [h]
  cases Nat.blt 0 pb <;> cases Nat.beq (length bs) pb <;> rfl

/-- **`Trusted → MiniRust` soundness (`UCG#558` W1).** Whenever a `Trusted`
8-byte stream is coherent with `ptrBytes = 8`, both authorities decode it to the
same address with the same (projected) provenance: `Trusted` to a `Value.ptr`
(for raw pointers and references alike) and MiniRust to a `ThinPointer` with
`some` provenance. -/
theorem coherent_decode_agreement {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte) (f : PtrByteFrag)
    (isRef : Bool) (hlen : bs.length = 8)
    (h : abstractBytesCoherentPtrProv? bs = some f) (hw : f.ptrBytes = 8) :
    ∃ data, trData bs = some data ∧
      thinDecode isRef 8 bs =
        some (.ptr { allocId := f.allocId, offsetBytes := Interp.leValue data } 8) ∧
      Interp.decodePtrM (M := M) (projBytes pv bs) =
        .ok (some { addr := ((Interp.leValue data : Nat) : Int),
                    provenance := some (pv f.allocId f.tag) }) := by
  obtain ⟨_, _, hc⟩ := (coherent?_eq_some_iff bs f).mp h
  obtain ⟨data, hd⟩ := trCoh_data _ _ _ _ bs 0 hc
  have hbits : decodeLittleEndianBits bs = some (Interp.leValue data) := by
    rw [bits_eq_leValue, hd]
    rfl
  refine ⟨data, hd, thinDecode_coherent isRef 8 bs _ f (by decide) hlen hbits h hw, ?_⟩
  rw [decodePtrM_proj pv bs hlen, hd, trusted_coherent_implies_minirust_retains pv bs f h]
  rfl

/-- `decodeScalarLayoutBytesNoForge` at a pointer scalar layout on a coherent stream. -/
theorem scalarLayoutPtr_coherent (addrSpace : Nat)
    (vr : Trusted.Rustc.V2026_08_01.Layout.WrappingRange) (bs : List AbstractByte) (bits : Nat)
    (f : PtrByteFrag) (policy : Ptr2IntTransmutePolicy) (hlen : bs.length = 8)
    (hbits : decodeLittleEndianBits bs = some bits)
    (h : abstractBytesCoherentPtrProv? bs = some f) (hw : f.ptrBytes = 8) :
    decodeScalarLayoutBytesNoForge (.initialized (.pointer addrSpace) vr) bs policy 8 =
      some (.ptr { allocId := f.allocId, offsetBytes := bits } 8) := by
  have e2 : Nat.beq (length bs) 8 = true := (nat_beq_iff _ _).mpr hlen
  have e3 : Nat.beq f.ptrBytes 8 = true := (nat_beq_iff _ _).mpr hw
  unfold decodeScalarLayoutBytesNoForge
  simp only [e2, hbits, h, e3]

/-- `decodeScalarLayoutBytesNoForge` at a pointer scalar layout on an incoherent
stream never forges provenance: the result is an integer scalar or invalid. -/
theorem scalarLayoutPtr_incoherent (addrSpace : Nat)
    (vr : Trusted.Rustc.V2026_08_01.Layout.WrappingRange) (bs : List AbstractByte) (bits : Nat)
    (policy : Ptr2IntTransmutePolicy) (hlen : bs.length = 8)
    (hbits : decodeLittleEndianBits bs = some bits)
    (h : abstractBytesCoherentPtrProv? bs = none) :
    decodeScalarLayoutBytesNoForge (.initialized (.pointer addrSpace) vr) bs policy 8 =
      (match wrappingRangeContains vr bits with
       | true => some (.scalar ⟨bits, 8⟩)
       | false => none) := by
  have e2 : Nat.beq (length bs) 8 = true := (nat_beq_iff _ _).mpr hlen
  unfold decodeScalarLayoutBytesNoForge
  simp only [e2, hbits, h]
  cases wrappingRangeContains vr bits <;> rfl

/-- `decodeScalarLayoutBytesNoForge` at a union pointer scalar layout on a coherent stream, for
any positive pointer width `pb` (including 32-bit `4` and 64-bit `8`). -/
theorem scalarLayoutPtr_union_coherent (addrSpace pb : Nat) (bs : List AbstractByte) (bits : Nat)
    (f : PtrByteFrag) (policy : Ptr2IntTransmutePolicy) (h0 : 0 < pb) (hlen : bs.length = pb)
    (hbits : decodeLittleEndianBits bs = some bits)
    (h : abstractBytesCoherentPtrProv? bs = some f) (hw : f.ptrBytes = pb) :
    decodeScalarLayoutBytesNoForge (.union (.pointer addrSpace)) bs policy pb =
      some (.ptr { allocId := f.allocId, offsetBytes := bits } pb) := by
  have hne : Nat.beq pb 0 = false := by cases pb with | zero => omega | succ _ => rfl
  have e2 : Nat.beq (length bs) pb = true := (nat_beq_iff _ _).mpr hlen
  have e3 : Nat.beq f.ptrBytes pb = true := (nat_beq_iff _ _).mpr hw
  unfold decodeScalarLayoutBytesNoForge scalarLayoutByteWidth primitiveKindByteWidth
  simp only [hne, e2, hbits, h, e3]

/-- `decodeScalarLayoutBytesNoForge` at a union pointer scalar layout on an incoherent stream never
forges provenance, for any positive pointer width `pb` (32-bit `4` or 64-bit `8`). -/
theorem scalarLayoutPtr_union_incoherent (addrSpace pb : Nat) (bs : List AbstractByte) (bits : Nat)
    (policy : Ptr2IntTransmutePolicy) (h0 : 0 < pb) (hlen : bs.length = pb)
    (hbits : decodeLittleEndianBits bs = some bits)
    (h : abstractBytesCoherentPtrProv? bs = none) :
    decodeScalarLayoutBytesNoForge (.union (.pointer addrSpace)) bs policy pb =
      some (.scalar ⟨bits, pb⟩) := by
  have hne : Nat.beq pb 0 = false := by cases pb with | zero => omega | succ _ => rfl
  have e2 : Nat.beq (length bs) pb = true := (nat_beq_iff _ _).mpr hlen
  unfold decodeScalarLayoutBytesNoForge scalarLayoutByteWidth primitiveKindByteWidth
  simp only [hne, e2, hbits, h]

/-- **UCG#630 W5 law**: `decodeScalarLayoutBytesNoForge` under `.strictUcg630Ub` rejects any
provenance-bearing byte stream at non-pointer integer scalar layouts (both `.initialized` and
`.union`). -/
theorem scalarLayoutNonPtr_strictUb_rejects_prov (bitWidth : Nat) (signed : Bool)
    (vr : Trusted.Rustc.V2026_08_01.Layout.WrappingRange) (pb : Nat) (bs : List AbstractByte)
    (hp : abstractBytesHaveProv bs = true) :
    decodeScalarLayoutBytesNoForge (.initialized (.int bitWidth signed) vr) bs .strictUcg630Ub pb = none ∧
    decodeScalarLayoutBytesNoForge (.union (.int bitWidth signed)) bs .strictUcg630Ub pb = none := by
  constructor <;> (
    unfold decodeScalarLayoutBytesNoForge
    cases scalarLayoutByteWidth _ pb with
    | none => rfl
    | some sz =>
      dsimp only
      cases Nat.beq (length bs) sz <;> simp [hp])

/-! ### §5. Exact encoding and intact round trips -/

theorem proj_encodeAux {M : Type} [Gen.Memory M] (pv : Nat → Nat → Gen.Memory.Provenance M)
    (a t o pb : Nat) :
    ∀ (n bits idx : Nat),
      projBytes pv (encodePtrBytesAux a t o pb bits idx n) =
        Interp.encodePtrBytesM (M := M) (some (pv a t)) idx (Interp.leBytes bits n)
  | 0, _, _ => rfl
  | n + 1, bits, idx => by
      have ih := proj_encodeAux pv a t o pb n (bits / 256) (idx + 1)
      show Gen.AbstractByte.Init (UInt8.ofNat bits) (some (projFrag pv ⟨a, t, idx, o, pb⟩)) ::
          projBytes pv (encodePtrBytesAux a t o pb (bits / 256) (idx + 1) n) =
        Gen.AbstractByte.Init (UInt8.ofNat (bits % 256)) (some ⟨pv a t, (idx : Int)⟩) ::
          Interp.encodePtrBytesM (M := M) (some (pv a t)) (idx + 1) (Interp.leBytes (bits / 256) n)
      rw [u8_ofNat_mod, ih]
      rfl

/-- **Exact pointer byte encoding.** The projection of the `Trusted` encoding of
a provenance-carrying pointer is exactly the MiniRust `encode_ptr` byte list of
the same address and the projected provenance. -/
theorem proj_encodePtrBytes {M : Type} [Gen.Memory M] (pv : Nat → Nat → Gen.Memory.Provenance M)
    (bits pb a t : Nat) :
    projBytes pv (encodePtrBytes bits pb a t) =
      Interp.encodePtrBytesM (M := M) (some (pv a t)) 0 (Interp.leBytes bits pb) :=
  proj_encodeAux pv a t _ pb pb bits 0

/-- A provenance-free pointer (`encodePlainLittleEndianBytes`) projects to the
MiniRust encoding of a pointer without provenance. -/
theorem proj_plain_bytes {M : Type} [Gen.Memory M] (pv : Nat → Nat → Gen.Memory.Provenance M) :
    ∀ (n bits idx : Nat),
      projBytes pv (encodePlainLittleEndianBytes bits n) =
        Interp.encodePtrBytesM (M := M) none idx (Interp.leBytes bits n)
  | 0, _, _ => rfl
  | n + 1, bits, idx => by
      have ih := proj_plain_bytes pv n (bits / 256) (idx + 1)
      show Gen.AbstractByte.Init (UInt8.ofNat bits) none ::
          projBytes pv (encodePlainLittleEndianBytes (bits / 256) n) =
        Gen.AbstractByte.Init (UInt8.ofNat (bits % 256)) none ::
          Interp.encodePtrBytesM (M := M) none (idx + 1) (Interp.leBytes (bits / 256) n)
      rw [u8_ofNat_mod, ih]

/-- **MiniRust `encode_ptr` agrees with `Trusted` on every valid 64-bit pointer.** -/
theorem encodePtrM_proj {M : Type} [Gen.Memory M] (pv : Nat → Nat → Gen.Memory.Provenance M)
    (addr a t : Nat) (h : addr < 2 ^ 64) :
    Interp.encodePtrM (M := M) { addr := (addr : Int), provenance := some (pv a t) } =
      .ok (projBytes pv (encodePtrBytes addr 8 a t)) :=
  (encodePtrM_of_encode (M := M) { addr := (addr : Int), provenance := some (pv a t) }
      (Interp.leBytes addr 8) (endianness_encode_ptr addr h)).trans
    (congrArg Except.ok (proj_encodePtrBytes (M := M) pv addr 8 a t).symm)

/-- The `BasicMemory`-specialized `encode_ptr` agrees with `Trusted` as well. -/
theorem encodePtr_proj (addr a t : Nat) (h : addr < 2 ^ 64) :
    Interp.encodePtr { addr := (addr : Int), provenance := some (bmProv a t) } =
      .ok (projBytes bmProv (encodePtrBytes addr 8 a t)) :=
  (encodePtr_of_encode { addr := (addr : Int), provenance := some (bmProv a t) }
      (Interp.leBytes addr 8) (endianness_encode_ptr addr h)).trans
    (congrArg Except.ok ((encodePtrBytes_eq_M _ _ 0).trans
      (proj_encodePtrBytes (M := Interp.BM) bmProv addr 8 a t).symm))

/-- The `Trusted` untyped encoding of a pointer value is `encodePtrBytes`. -/
theorem encodeUntyped_ptr (fuel : Nat) (p : ProvenancePtr) (sz : Nat) (hsz : 0 < sz) :
    encodeUntypedValueToBytes (fuel + 1) (.ptr p sz) =
      some (encodePtrBytes p.offsetBytes sz p.allocId p.tag) := by
  cases sz with
  | zero => omega
  | succ n => rfl

/-- **`encodeValueToBytes` on thin pointers.** For any thin pointer type (`.rawPtr`, `.ref`,
`.fnPtr`) at target pointer width `pb > 0`, `encodeValueToBytes` produces `encodePtrBytes`. -/
theorem encodeValueToBytes_thinPtr (fuel : Nat) (layouts : LayoutTable) (ty : Ty)
    (p : ProvenancePtr) (pb : Nat) (hpb : layoutPointerBytes layouts = pb) (h0 : 0 < pb)
    (hty : (∃ m pt, ty.kind = .rawPtr m pt ∧ thinPointee pt = true) ∨
           (∃ m pt, ty.kind = .ref m pt ∧ thinPointee pt = true) ∨
           (∃ a r s ab, ty.kind = .fnPtr a r s ab)) :
    encodeValueToBytes (fuel + 1) layouts ty (.ptr p pb) =
      some (encodePtrBytes p.offsetBytes pb p.allocId p.tag) := by
  obtain ⟨kind, lidx⟩ := ty
  have hblt : Nat.blt 0 pb = true := by rw [Nat.blt_eq]; exact h0
  have hnz : Nat.beq pb 0 = false := by cases pb with | zero => omega | succ _ => rfl
  rcases hty with ⟨m, pt, hk, hthin⟩ | ⟨m, pt, hk, hthin⟩ | ⟨a, r, s, ab, hk⟩
  · dsimp only at hk; subst hk
    cases pt <;> first
      | (cases hthin; done)
      | (unfold encodeValueToBytes; rw [hpb]; simp [hblt, encodeScalarBytes, hnz, encodeLittleEndianBytes])
  · dsimp only at hk; subst hk
    cases pt <;> first
      | (cases hthin; done)
      | (unfold encodeValueToBytes; rw [hpb]; simp [hblt, encodeScalarBytes, hnz, encodeLittleEndianBytes])
  · dsimp only at hk; subst hk
    unfold encodeValueToBytes; rw [hpb]; simp [hblt, encodeScalarBytes, hnz, encodeLittleEndianBytes]

theorem bits_encodeAux (a t o pb : Nat) :
    ∀ (n bits idx : Nat),
      decodeLittleEndianBits (encodePtrBytesAux a t o pb bits idx n) = some (bits % 256 ^ n)
  | 0, bits, _ => by
      show some 0 = some (bits % 256 ^ 0)
      rw [Nat.pow_zero, Nat.mod_one]
  | n + 1, bits, idx => by
      have ih := bits_encodeAux a t o pb n (bits / 256) (idx + 1)
      show (match decodeLittleEndianBits
            (encodePtrBytesAux a t o pb (bits / 256) (idx + 1) n) with
        | some highBits =>
          some (Nat.add (UInt8.ofNat bits).toBitVec.toNat (Nat.mul 256 highBits))
        | none => none) = some (bits % 256 ^ (n + 1))
      rw [ih]
      show some ((UInt8.ofNat bits).toNat + 256 * (bits / 256 % 256 ^ n)) =
        some (bits % 256 ^ (n + 1))
      rw [u8_ofNat_toNat, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]

theorem trCoh_encodeAux (a t o pb : Nat) :
    ∀ (n bits idx : Nat), idx + n = pb →
      TrCoh a t o pb idx (encodePtrBytesAux a t o pb bits idx n)
  | 0, _, idx, h => by
      show idx = pb
      omega
  | n + 1, bits, idx, h =>
      And.intro ⟨_, rfl⟩
        (trCoh_encodeAux a t o pb n (bits / 256) (idx + 1) (by omega))

/-- The `Trusted` encoding of a pointer is coherent, with the head fragment of the pointer. -/
theorem coherent?_encodePtrBytes (bits pb a t : Nat) (hpb : 0 < pb) :
    abstractBytesCoherentPtrProv? (encodePtrBytes bits pb a t) =
      some ⟨a, t, 0, normPtrByteOffset pb bits, pb⟩ :=
  (coherent?_eq_some_iff _ _).mpr ⟨hpb, rfl, trCoh_encodeAux a t _ pb pb bits 0 (by omega)⟩

theorem encodePtrBytes_length (bits pb a t : Nat) : (encodePtrBytes bits pb a t).length = pb := by
  have := trCoh_length a t _ pb _ 0 (trCoh_encodeAux a t (normPtrByteOffset pb bits) pb pb bits 0
    (by omega))
  rw [Nat.zero_add] at this
  exact this

/-- Every byte of an encoded pointer is the fragment of its own position. -/
theorem encodePtrBytes_get (bits pb a t i : Nat) (b : AbstractByte)
    (h : (encodePtrBytes bits pb a t)[i]? = some b) :
    ∃ v, b = .init v (some ⟨a, t, i, normPtrByteOffset pb bits, pb⟩) := by
  have := trCoh_get a t _ pb _ 0
    (trCoh_encodeAux a t (normPtrByteOffset pb bits) pb pb bits 0 (by omega)) i b h
  rw [Nat.zero_add] at this
  exact this

/-- **Intact `Trusted` round trip** (`encodePtrBytes → decodePtrBytesNoForge`), for
raw pointers and references, at any positive pointer width. -/
theorem thinDecode_encodePtrBytes (isRef : Bool) (bits pb a t : Nat) (hpb : 0 < pb) :
    thinDecode isRef pb (encodePtrBytes bits pb a t) =
      some (.ptr { allocId := a, offsetBytes := bits % 256 ^ pb } pb) :=
  thinDecode_coherent isRef pb _ _ ⟨a, t, 0, normPtrByteOffset pb bits, pb⟩ hpb
    (encodePtrBytes_length bits pb a t) (bits_encodeAux a t _ pb pb bits 0)
    (coherent?_encodePtrBytes bits pb a t hpb) rfl

/-- **Intact MiniRust round trip on the projected `Trusted` encoding.** For every
valid 64-bit pointer, MiniRust `decode_ptr` of the projected `Trusted` bytes is
the same address with the projected provenance. -/
theorem decodePtrM_proj_encodePtrBytes {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (addr a t : Nat) (h : addr < 2 ^ 64) :
    Interp.decodePtrM (M := M) (projBytes pv (encodePtrBytes addr 8 a t)) =
      .ok (some { addr := (addr : Int), provenance := some (pv a t) }) := by
  obtain ⟨data, hd, _, hm⟩ := coherent_decode_agreement (M := M) pv (encodePtrBytes addr 8 a t)
    ⟨a, t, 0, normPtrByteOffset 8 addr, 8⟩ false (encodePtrBytes_length addr 8 a t)
    (coherent?_encodePtrBytes addr 8 a t (by decide)) rfl
  have hbits : some (Interp.leValue data) = some (addr % 256 ^ 8) := by
    have h1 := bits_eq_leValue (encodePtrBytes addr 8 a t)
    rw [hd, bits_encodeAux a t _ 8 8 addr 0] at h1
    exact h1.symm
  injection hbits with hbits
  have hmod : addr % 256 ^ 8 = addr := Nat.mod_eq_of_lt (by
    have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    omega)
  rw [hm, hbits, hmod]

/-- **Union raw-byte carrier round trip**: the lossless `Value` carrier of an
abstract byte decodes back to exactly that byte. -/
theorem rawCarrier_roundtrip (b : AbstractByte) :
    decodeRawAbstractByteVal? (encodeRawAbstractByteVal b) = some b := by
  cases b with
  | uninit => rfl
  | init v pr =>
      cases pr with
      | none =>
          show decodeRawAbstractByteVal? (.scalar ⟨v.toBitVec.toNat, 1⟩) = _
          have hv : UInt8.ofNat v.toBitVec.toNat = v := UInt8.ofNat_toNat
          unfold decodeRawAbstractByteVal?
          split <;> simp_all <;> (rename_i hbits; subst hbits; exact UInt8.ofNat_toNat)
      | some f =>
          show some (AbstractByte.init (UInt8.ofNat v.toBitVec.toNat) (some _)) = _
          have hv : UInt8.ofNat v.toBitVec.toNat = v := UInt8.ofNat_toNat
          rw [hv]

theorem rawCarrier_list_roundtrip :
    ∀ bs : List AbstractByte,
      decodeRawAbstractByteVals? (bs.map encodeRawAbstractByteVal) = some bs
  | [] => rfl
  | b :: rest => by
      show (match decodeRawAbstractByteVal? (encodeRawAbstractByteVal b),
          decodeRawAbstractByteVals? (rest.map encodeRawAbstractByteVal) with
        | some b', some bs' => some (b' :: bs')
        | _, _ => none) = some (b :: rest)
      rw [rawCarrier_roundtrip, rawCarrier_list_roundtrip rest]

/-- **Intact bytewise copy through the union raw-byte carrier.** A pointer moved
byte by byte through the carrier (`[u8; 8]`, `MaybeUninit`, or a union) decodes,
in both authorities, to exactly the original address and provenance. -/
theorem rawCarrier_ptr_roundtrip {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (isRef : Bool) (addr a t : Nat)
    (h : addr < 2 ^ 64) :
    ∃ bs, decodeRawAbstractByteVals?
        ((encodePtrBytes addr 8 a t).map encodeRawAbstractByteVal) = some bs ∧
      thinDecode isRef 8 bs = some (.ptr { allocId := a, offsetBytes := addr } 8) ∧
      Interp.decodePtrM (M := M) (projBytes pv bs) =
        .ok (some { addr := (addr : Int), provenance := some (pv a t) }) := by
  refine ⟨_, rawCarrier_list_roundtrip _, ?_, decodePtrM_proj_encodePtrBytes pv addr a t h⟩
  have hmod : addr % 256 ^ 8 = addr := Nat.mod_eq_of_lt (by
    have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    omega)
  have := thinDecode_encodePtrBytes isRef addr 8 a t (by decide)
  rw [hmod] at this
  exact this

/-! ### §6. `UCG#558` W1: both authorities strip provenance on every non-intact stream -/

/-- **Arbitrary non-identity permutation (`Trusted`).** A stream holding at
position `i` the byte that an encoded pointer carries at a different position
`j` has no coherent provenance. -/
theorem permuted_strips_trusted (bs : List AbstractByte) (bits pb a t i j : Nat)
    (b : AbstractByte) (hij : i ≠ j) (hb : bs[i]? = some b)
    (hj : (encodePtrBytes bits pb a t)[j]? = some b) :
    abstractBytesCoherentPtrProv? bs = none := by
  obtain ⟨v, hv⟩ := encodePtrBytes_get bits pb a t j b hj
  subst hv
  refine coherent?_none_of_bad_position bs i _ hb ?_
  intro v' f hf
  injection hf with _ hf
  injection hf with hf
  subst hf
  exact fun h => hij h.symm

/-- **Arbitrary non-identity permutation (MiniRust).** The projected stream loses
its provenance in `decode_ptr` as well. -/
theorem permuted_strips_minirust {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte)
    (bits pb a t i j : Nat) (b : AbstractByte) (hij : i ≠ j) (hb : bs[i]? = some b)
    (hj : (encodePtrBytes bits pb a t)[j]? = some b) :
    mrProvM M (projBytes pv bs) = none := by
  obtain ⟨v, hv⟩ := encodePtrBytes_get bits pb a t j b hj
  subst hv
  refine mrProvM_eq_none_of_bad _ i _ (projBytes_get pv bs i _ hb) ?_
  intro v' fr hf
  have hf' : Gen.AbstractByte.Init v
      (some (projFrag pv ⟨a, t, j, normPtrByteOffset pb bits, pb⟩)) = .Init v' (some fr) := hf
  injection hf' with _ hf'
  injection hf' with hf'
  subst hf'
  show ((j : Nat) : Int) ≠ (i : Int)
  omega

/-- Swap of byte 0 and byte 1. -/
def swap01 : List AbstractByte → List AbstractByte
  | x :: y :: rest => y :: x :: rest
  | bs => bs

/-- Byte 0 repeated over the whole stream. -/
def dupHead : List AbstractByte → List AbstractByte
  | x :: rest => x :: rest.map (fun _ => x)
  | [] => []

/-- **8-byte full reversal** strips provenance in both authorities, for every
address (including the all-zero image of offset `0`) and provenance. -/
theorem reversal_strips {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bits a t : Nat) :
    abstractBytesCoherentPtrProv? (encodePtrBytes bits 8 a t).reverse = none ∧
      mrProvM M (projBytes pv (encodePtrBytes bits 8 a t).reverse) = none :=
  ⟨permuted_strips_trusted _ bits 8 a t 0 7 _ (by decide) rfl rfl,
   permuted_strips_minirust pv _ bits 8 a t 0 7 _ (by decide) rfl rfl⟩

/-- **Byte-0 / byte-1 swap** strips provenance in both authorities. -/
theorem swap01_strips {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bits a t : Nat) :
    abstractBytesCoherentPtrProv? (swap01 (encodePtrBytes bits 8 a t)) = none ∧
      mrProvM M (projBytes pv (swap01 (encodePtrBytes bits 8 a t))) = none :=
  ⟨permuted_strips_trusted _ bits 8 a t 0 1 _ (by decide) rfl rfl,
   permuted_strips_minirust pv _ bits 8 a t 0 1 _ (by decide) rfl rfl⟩

/-- **Byte 0 duplicated 8×** strips provenance in both authorities. -/
theorem dupHead_strips {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bits a t : Nat) :
    abstractBytesCoherentPtrProv? (dupHead (encodePtrBytes bits 8 a t)) = none ∧
      mrProvM M (projBytes pv (dupHead (encodePtrBytes bits 8 a t))) = none :=
  ⟨permuted_strips_trusted _ bits 8 a t 1 0 _ (by decide) rfl rfl,
   permuted_strips_minirust pv _ bits 8 a t 1 0 _ (by decide) rfl rfl⟩

/-- **End-to-end decoder stripping (`UCG#558` W1)** for full reversal, byte-0/1 swap, and head
duplication: `Trusted` decodes raw pointers to provenance-free `.scalar` and rejects references
(`none`), while MiniRust `decodePtrM` returns `.ok (some ⟨addr, none⟩)`. -/
theorem w1_transforms_decode_strips {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bits a t : Nat) :
    let bsRev := (encodePtrBytes bits 8 a t).reverse
    let bsSwap := swap01 (encodePtrBytes bits 8 a t)
    let bsDup := dupHead (encodePtrBytes bits 8 a t)
    (∃ d, trData bsRev = some d ∧ thinDecode false 8 bsRev = some (.scalar ⟨Interp.leValue d, 8⟩) ∧
      thinDecode true 8 bsRev = none ∧
      Interp.decodePtrM (M := M) (projBytes pv bsRev) =
        .ok (some { addr := ((Interp.leValue d : Nat) : Int), provenance := none })) ∧
    (∃ d, trData bsSwap = some d ∧ thinDecode false 8 bsSwap = some (.scalar ⟨Interp.leValue d, 8⟩) ∧
      thinDecode true 8 bsSwap = none ∧
      Interp.decodePtrM (M := M) (projBytes pv bsSwap) =
        .ok (some { addr := ((Interp.leValue d : Nat) : Int), provenance := none })) ∧
    (∃ d, trData bsDup = some d ∧ thinDecode false 8 bsDup = some (.scalar ⟨Interp.leValue d, 8⟩) ∧
      thinDecode true 8 bsDup = none ∧
      Interp.decodePtrM (M := M) (projBytes pv bsDup) =
        .ok (some { addr := ((Interp.leValue d : Nat) : Int), provenance := none })) := by
  intro bsRev bsSwap bsDup
  have hstep : ∀ (bs : List AbstractByte) (data : List UInt8),
      bs.length = 8 → trData bs = some data →
      abstractBytesCoherentPtrProv? bs = none →
      mrProvM M (projBytes pv bs) = none →
      ∃ d, trData bs = some d ∧ thinDecode false 8 bs = some (.scalar ⟨Interp.leValue d, 8⟩) ∧
        thinDecode true 8 bs = none ∧
        Interp.decodePtrM (M := M) (projBytes pv bs) =
          .ok (some { addr := ((Interp.leValue d : Nat) : Int), provenance := none }) := by
    intro bs data hlen hd htr hmr
    have hbits : decodeLittleEndianBits bs = some (Interp.leValue data) := by
      rw [bits_eq_leValue, hd]; rfl
    refine ⟨data, hd, thinDecode_raw_incoherent 8 bs _ (by decide) hlen hbits htr,
      thinDecode_ref_incoherent 8 bs htr, ?_⟩
    rw [decodePtrM_proj pv bs hlen, hd, hmr]; rfl
  refine ⟨?_, ?_, ?_⟩
  · exact hstep bsRev _ rfl rfl (reversal_strips (M := M) pv bits a t).1 (reversal_strips (M := M) pv bits a t).2
  · exact hstep bsSwap _ rfl rfl (swap01_strips (M := M) pv bits a t).1 (swap01_strips (M := M) pv bits a t).2
  · exact hstep bsDup _ rfl rfl (dupHead_strips (M := M) pv bits a t).1 (dupHead_strips (M := M) pv bits a t).2

/-- **Mixed provenance** (`Trusted`): fragments of two allocations or two tags. -/
theorem mixed_provenance_strips_trusted (bs : List AbstractByte) (i j : Nat) (vi vj : UInt8)
    (fi fj : PtrByteFrag)
    (hi : bs[i]? = some (.init vi (some fi))) (hj : bs[j]? = some (.init vj (some fj)))
    (hne : fi.allocId ≠ fj.allocId ∨ fi.tag ≠ fj.tag) :
    abstractBytesCoherentPtrProv? bs = none :=
  coherent?_none_of_field_mismatch bs i j vi vj fi fj hi hj
    (hne.elim Or.inl (fun h => Or.inr (Or.inl h)))

/-- **Mixed provenance** (MiniRust): fragments whose projected provenances differ. -/
theorem mixed_provenance_strips_minirust {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte) (i j : Nat)
    (vi vj : UInt8) (fi fj : PtrByteFrag)
    (hi : bs[i]? = some (.init vi (some fi))) (hj : bs[j]? = some (.init vj (some fj)))
    (hne : pv fi.allocId fi.tag ≠ pv fj.allocId fj.tag) :
    mrProvM M (projBytes pv bs) = none :=
  mrProvM_eq_none_of_prov_mismatch _ i j vi vj (projFrag pv fi) (projFrag pv fj)
    (projBytes_get pv bs i _ hi) (projBytes_get pv bs j _ hj) hne

/-- **Missing provenance** (`Trusted`): a plain byte anywhere in the stream (in
particular an all-plain integer image) never yields provenance — no
integer-to-pointer forging. -/
theorem missing_provenance_strips_trusted (bs : List AbstractByte) (i : Nat) (v : UInt8)
    (hb : bs[i]? = some (.init v none)) :
    abstractBytesCoherentPtrProv? bs = none := by
  refine coherent?_none_of_bad_position bs i _ hb ?_
  intro v' f hf
  injection hf with _ hf
  cases hf

/-- **Missing provenance** (MiniRust). -/
theorem missing_provenance_strips_minirust {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte) (i : Nat) (v : UInt8)
    (hb : bs[i]? = some (.init v none)) :
    mrProvM M (projBytes pv bs) = none := by
  refine mrProvM_eq_none_of_bad _ i _ (projBytes_get pv bs i _ hb) ?_
  intro v' fr hf
  have hf' : Gen.AbstractByte.Init v (none : Option (Gen.ProvenanceFrag (Gen.Memory.Provenance M))) =
      .Init v' (some fr) := hf
  injection hf' with _ hf'
  cases hf'

/-- **Any `.uninit` byte** (`Trusted`): the pointer decode fails, for raw pointers
and references alike. -/
theorem uninit_rejected_trusted (isRef : Bool) (pb : Nat) (bs : List AbstractByte)
    (h : AbstractByte.uninit ∈ bs) : thinDecode isRef pb bs = none := by
  refine thinDecode_uninit isRef pb bs ?_
  rw [bits_eq_leValue, trData_none_of_uninit bs h]
  rfl

/-- **Any `.uninit` byte** (MiniRust): `decode_ptr` returns `None`. -/
theorem uninit_rejected_minirust {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte) (hlen : bs.length = 8)
    (h : AbstractByte.uninit ∈ bs) :
    Interp.decodePtrM (M := M) (projBytes pv bs) = .ok none := by
  rw [decodePtrM_proj pv bs hlen, trData_none_of_uninit bs h]
  rfl

/-! ### §7. `UCG#558` W2 / `rust#148259`: offset splices and the strict refinement -/

/-- **`Trusted` strips an offset splice.** A stream holding byte `i` of the
encoding of `bits₁` and byte `j` of the encoding of `bits₂` — the *same*
allocation and tag — has no coherent provenance when the two normalized
originating offsets differ. -/
theorem offset_splice_trusted_strips (bs : List AbstractByte) (bits₁ bits₂ pb a t i j : Nat)
    (b₁ b₂ : AbstractByte)
    (h₁ : bs[i]? = some b₁) (e₁ : (encodePtrBytes bits₁ pb a t)[i]? = some b₁)
    (h₂ : bs[j]? = some b₂) (e₂ : (encodePtrBytes bits₂ pb a t)[j]? = some b₂)
    (hne : normPtrByteOffset pb bits₁ ≠ normPtrByteOffset pb bits₂) :
    abstractBytesCoherentPtrProv? bs = none := by
  obtain ⟨v₁, hv₁⟩ := encodePtrBytes_get bits₁ pb a t i b₁ e₁
  obtain ⟨v₂, hv₂⟩ := encodePtrBytes_get bits₂ pb a t j b₂ e₂
  subst hv₁
  subst hv₂
  exact coherent?_none_of_field_mismatch bs i j v₁ v₂ _ _ h₁ h₂ (Or.inr (Or.inr (Or.inl hne)))

/-- **Vendored MiniRust retains provenance on every same-provenance splice.** A
non-empty stream each of whose bytes is the in-position byte of the encoding of
`bits₁` or of `bits₂` (same allocation and tag) keeps `some (pv a t)` in
`decode_ptr`: MiniRust's `ProvenanceFrag { provenance, position }` cannot tell
the two originating pointers apart. -/
theorem offset_splice_minirust_retains {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte)
    (bits₁ bits₂ pb a t : Nat) (hne : bs ≠ [])
    (hsel : ∀ (i : Nat) (b : AbstractByte), bs[i]? = some b →
      (encodePtrBytes bits₁ pb a t)[i]? = some b ∨ (encodePtrBytes bits₂ pb a t)[i]? = some b) :
    mrProvM M (projBytes pv bs) = some (pv a t) := by
  refine mrProvM_eq_some_of_get _ _ ?_ ?_
  · intro h
    have hl := congrArg List.length h
    rw [projBytes_length] at hl
    cases bs with
    | nil => exact hne rfl
    | cons _ _ => cases hl
  · intro i b' hb'
    cases hbi : bs[i]? with
    | none =>
        have := projBytes_get pv bs i
        unfold projBytes at hb'
        rw [List.getElem?_map, hbi] at hb'
        cases hb'
    | some b =>
        have hp := projBytes_get pv bs i b hbi
        rw [hp] at hb'
        injection hb' with hb'
        subst hb'
        rcases hsel i b hbi with h | h
        · obtain ⟨v, hv⟩ := encodePtrBytes_get bits₁ pb a t i b h
          subst hv
          exact ⟨v, rfl⟩
        · obtain ⟨v, hv⟩ := encodePtrBytes_get bits₂ pb a t i b h
          subst hv
          exact ⟨v, rfl⟩

/-- **End-to-end offset-splice decoder divergence (`DIV-MR-OFFSET-SPLICE`, `UCG#558` W2).**
For any 8-byte same-provenance splice `bs` drawing each byte in-position from `bits₁` or `bits₂`
(with at least one byte from each and `normPtrByteOffset 8 bits₁ ≠ normPtrByteOffset 8 bits₂`):
`Trusted` strips provenance (`thinDecode false` → `.scalar`, `thinDecode true` → `none`), while
MiniRust `decodePtrM` retains `some (pv a t)` on the exact same decoded address. -/
theorem offset_splice_decode_divergence {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (bs : List AbstractByte)
    (bits₁ bits₂ a t i j : Nat) (b₁ b₂ : AbstractByte) (hlen : bs.length = 8)
    (hsel : ∀ (k : Nat) (b : AbstractByte), bs[k]? = some b →
      (encodePtrBytes bits₁ 8 a t)[k]? = some b ∨ (encodePtrBytes bits₂ 8 a t)[k]? = some b)
    (h₁ : bs[i]? = some b₁) (e₁ : (encodePtrBytes bits₁ 8 a t)[i]? = some b₁)
    (h₂ : bs[j]? = some b₂) (e₂ : (encodePtrBytes bits₂ 8 a t)[j]? = some b₂)
    (hne : normPtrByteOffset 8 bits₁ ≠ normPtrByteOffset 8 bits₂) :
    ∃ data, trData bs = some data ∧
      thinDecode false 8 bs = some (.scalar ⟨Interp.leValue data, 8⟩) ∧
      thinDecode true 8 bs = none ∧
      Interp.decodePtrM (M := M) (projBytes pv bs) =
        .ok (some { addr := ((Interp.leValue data : Nat) : Int),
                    provenance := some (pv a t) }) := by
  have htr := offset_splice_trusted_strips bs bits₁ bits₂ 8 a t i j b₁ b₂ h₁ e₁ h₂ e₂ hne
  have hneList : bs ≠ [] := by intro h; subst h; cases hlen
  have hmr := offset_splice_minirust_retains (M := M) pv bs bits₁ bits₂ 8 a t hneList hsel
  have hdata : ∃ data, trData bs = some data := by
    have hall : ∀ (k : Nat) (b : AbstractByte), bs[k]? = some b → ∃ (v : UInt8) (pr : Option PtrByteFrag), b = .init v pr := by
      intro k b hk
      rcases hsel k b hk with h | h
      · obtain ⟨v, hv⟩ := encodePtrBytes_get bits₁ 8 a t k b h; exact ⟨v, _, hv⟩
      · obtain ⟨v, hv⟩ := encodePtrBytes_get bits₂ 8 a t k b h; exact ⟨v, _, hv⟩
    have aux : ∀ (l : List AbstractByte),
        (∀ (k : Nat) (b : AbstractByte), l[k]? = some b → ∃ (v : UInt8) (pr : Option PtrByteFrag), b = .init v pr) → ∃ d, trData l = some d := by
      intro l
      induction l with
      | nil => intro _; exact ⟨[], rfl⟩
      | cons x xs ih =>
        intro hl
        obtain ⟨v, pr, rfl⟩ := hl 0 x rfl
        obtain ⟨d, hd⟩ := ih (fun k b hk => hl (k + 1) b hk)
        exact ⟨v :: d, by show (trData xs).map (v :: ·) = _; rw [hd]; rfl⟩
    exact aux bs hall
  obtain ⟨data, hd⟩ := hdata
  have hbits : decodeLittleEndianBits bs = some (Interp.leValue data) := by
    rw [bits_eq_leValue, hd]; rfl
  refine ⟨data, hd, thinDecode_raw_incoherent 8 bs _ (by decide) hlen hbits htr,
    thinDecode_ref_incoherent 8 bs htr, ?_⟩
  rw [decodePtrM_proj pv bs hlen, hd, hmr]
  rfl

/-- **Exact characterization of the refinement gap.** For an injective
provenance embedding, whenever MiniRust retains provenance on the projected
stream, `Trusted` strips it **if and only if** two fragments disagree on the
originating offset or the pointer width, or the fragment width is not the
stream length. (With a common width — every pointer of one target — the
converse of `trusted_retains_implies_minirust_retains` therefore fails
precisely on same-provenance splices of different originating offsets.) -/
theorem converse_gap_iff {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M)
    (hinj : ∀ a t a' t', pv a t = pv a' t' → a = a' ∧ t = t')
    (bs : List AbstractByte) (p : Gen.Memory.Provenance M)
    (hmr : mrProvM M (projBytes pv bs) = some p) :
    abstractBytesCoherentPtrProv? bs = none ↔
      ∃ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag), bs[i]? = some (.init vi (some fi)) ∧
        bs[j]? = some (.init vj (some fj)) ∧
        (fi.origOffset ≠ fj.origOffset ∨ fi.ptrBytes ≠ fj.ptrBytes ∨
          fi.ptrBytes ≠ bs.length) := by
  constructor
  · intro hnone
    apply Classical.byContradiction
    intro hno
    obtain ⟨hne, hcoh⟩ := (mrProvM_eq_some_iff _ _).mp hmr
    have hget := (mrCoh_iff_get p _ 0).mp hcoh
    have hall : ∀ (i : Nat) (b : AbstractByte), bs[i]? = some b →
        ∃ (v : UInt8) (f : PtrByteFrag),
          b = AbstractByte.init v (some f) ∧ pv f.allocId f.tag = p ∧ f.byteIdx = i := by
      intro i b hb
      obtain ⟨v, hv⟩ := hget i _ (projBytes_get pv bs i b hb)
      obtain ⟨f, hf, hfr⟩ := projByte_eq_init_some pv b v _ hv
      refine ⟨v, f, hf, congrArg Gen.ProvenanceFrag.provenance hfr, ?_⟩
      have hpos : ((f.byteIdx : Nat) : Int) = ((0 + i : Nat) : Int) :=
        congrArg Gen.ProvenanceFrag.position hfr
      omega
    cases bs with
    | nil => exact hne rfl
    | cons b0 rest =>
        obtain ⟨v0, f0, hf0, hp0, hi0⟩ := hall 0 b0 rfl
        subst hf0
        have hfields : ∀ (i : Nat) (b : AbstractByte),
            (AbstractByte.init v0 (some f0) :: rest)[i]? = some b →
            ∃ v, b = AbstractByte.init v
              (some ⟨f0.allocId, f0.tag, 0 + i, f0.origOffset, f0.ptrBytes⟩) := by
          intro i b hb
          obtain ⟨v, f, hf, hp, hi⟩ := hall i b hb
          subst hf
          obtain ⟨ha, ht⟩ := hinj _ _ _ _ (hp.trans hp0.symm)
          have ho : f.origOffset = f0.origOffset :=
            Decidable.byContradiction fun hne' =>
              hno ⟨i, 0, v, v0, f, f0, hb, rfl, Or.inl hne'⟩
          have hw : f.ptrBytes = f0.ptrBytes :=
            Decidable.byContradiction fun hne' =>
              hno ⟨i, 0, v, v0, f, f0, hb, rfl, Or.inr (Or.inl hne')⟩
          refine ⟨v, congrArg (fun x => AbstractByte.init v (some x)) (frag_ext _ _ ha ht ?_ ho hw)⟩
          show f.byteIdx = 0 + i
          omega
        have hlen : f0.ptrBytes = (AbstractByte.init v0 (some f0) :: rest).length :=
          Decidable.byContradiction fun hne' =>
            hno ⟨0, 0, v0, v0, f0, f0, rfl, rfl, Or.inr (Or.inr hne')⟩
        have hc := trCoh_of_get f0.allocId f0.tag f0.origOffset f0.ptrBytes _ 0 (by omega) hfields
        have hpos : 0 < f0.ptrBytes := by
          simp only [List.length_cons] at hlen
          omega
        have hsome := (coherent?_eq_some_iff _ f0).mpr ⟨hpos, hi0, hc⟩
        rw [hnone] at hsome
        cases hsome
  · rintro ⟨i, j, vi, vj, fi, fj, hi, hj, hne⟩
    cases h : abstractBytesCoherentPtrProv? bs with
    | none => rfl
    | some f =>
        obtain ⟨_, _, hc⟩ := (coherent?_eq_some_iff bs f).mp h
        obtain ⟨v1, h1⟩ := trCoh_get _ _ _ _ bs 0 hc i _ hi
        obtain ⟨v2, h2⟩ := trCoh_get _ _ _ _ bs 0 hc j _ hj
        have hl := trCoh_length _ _ _ _ bs 0 hc
        injection h1 with _ h1
        injection h1 with h1
        injection h2 with _ h2
        injection h2 with h2
        subst h1
        subst h2
        rcases hne with h | h | h
        · exact absurd rfl h
        · exact absurd rfl h
        · exact absurd (by show f.ptrBytes = bs.length; omega) h

/-! ### §8. Wide pointers -/

theorem take_append :
    ∀ (d m : List AbstractByte), takeAbstractBytes d.length (d ++ m) = d
  | [], m => by cases m <;> rfl
  | x :: d, m => by
      show x :: takeAbstractBytes d.length (d ++ m) = x :: d
      rw [take_append d m]

theorem drop_append :
    ∀ (d m : List AbstractByte), dropAbstractBytes d.length (d ++ m) = m
  | [], _ => rfl
  | _ :: d, m => drop_append d m

/-- The slice / `str` metadata half of `decodePtrBytesNoForge`: a plain integer
length; any provenance-carrying byte is rejected. -/
def sliceMetaDecode (pb : Nat) (metaBytes : List AbstractByte) : Option Value :=
  match decodeLittleEndianBits metaBytes with
  | .none => .none
  | .some metaBits =>
    match abstractBytesHaveProv metaBytes with
    | true => .none
    | false => .some (.scalar ⟨metaBits, pb⟩)

/-- **Wide slice pointers** (`&[T]`, `*const [T]`): the data half is decoded by
`thinDecode` and the length half by `sliceMetaDecode`. -/
theorem decodePtrBytesNoForge_slice (isRef : Bool) (elem : RigidTy) (d m : List AbstractByte)
    (h0 : 0 < d.length) (hm : m.length = d.length) :
    decodePtrBytesNoForge isRef (.slice elem) d.length (d ++ m) =
      (match thinDecode isRef d.length d, sliceMetaDecode d.length m with
       | some dv, some mv => some (.aggregate 0 [dv, mv])
       | _, _ => none) := by
  have e1 : Nat.blt 0 d.length = true := by
    rw [Nat.blt_eq]
    exact h0
  have e2 : Nat.beq (length (d ++ m)) (Nat.add d.length d.length) = true :=
    (nat_beq_iff _ _).mpr (by
      show (d ++ m).length = d.length + d.length
      rw [List.length_append, hm])
  unfold decodePtrBytesNoForge thinDecode
  simp only [e1, e2, take_append, drop_append]
  rfl

/-- **Wide `str` pointers** (`&str`, `*const str`) decode exactly as slices. -/
theorem decodePtrBytesNoForge_str (isRef : Bool) (d m : List AbstractByte)
    (h0 : 0 < d.length) (hm : m.length = d.length) :
    decodePtrBytesNoForge isRef .str d.length (d ++ m) =
      (match thinDecode isRef d.length d, sliceMetaDecode d.length m with
       | some dv, some mv => some (.aggregate 0 [dv, mv])
       | _, _ => none) := by
  have e1 : Nat.blt 0 d.length = true := by
    rw [Nat.blt_eq]
    exact h0
  have e2 : Nat.beq (length (d ++ m)) (Nat.add d.length d.length) = true :=
    (nat_beq_iff _ _).mpr (by
      show (d ++ m).length = d.length + d.length
      rw [List.length_append, hm])
  unfold decodePtrBytesNoForge thinDecode
  simp only [e1, e2, take_append, drop_append]
  rfl

/-- **Provenance-bearing slice metadata is rejected** — in particular the
swapped halves `metadata ++ data` of a wide pointer, whose "length" half is a
pointer image (`DIV-MR-PTR2INT`: MiniRust accepts it as an integer). -/
theorem slice_meta_with_provenance_rejected (isRef : Bool) (elem : RigidTy)
    (d m : List AbstractByte) (h0 : 0 < d.length) (hm : m.length = d.length)
    (hp : abstractBytesHaveProv m = true) :
    decodePtrBytesNoForge isRef (.slice elem) d.length (d ++ m) = none := by
  rw [decodePtrBytesNoForge_slice isRef elem d m h0 hm]
  unfold sliceMetaDecode
  rw [hp]
  cases thinDecode isRef d.length d <;> cases decodeLittleEndianBits m <;> rfl

/-- **Wide trait-object pointers (`&dyn Trait`, `*const dyn Trait`)**: both data and vtable halves
decode through `thinDecode`. -/
theorem decodePtrBytesNoForge_dyn (isRef : Bool) (tr : String) (d m : List AbstractByte)
    (h0 : 0 < d.length) (hm : m.length = d.length) :
    decodePtrBytesNoForge isRef (.dynamic tr) d.length (d ++ m) =
      (match thinDecode isRef d.length d, thinDecode isRef d.length m with
       | some dv, some mv => some (.aggregate 0 [dv, mv])
       | _, _ => none) := by
  have e1 : Nat.blt 0 d.length = true := by rw [Nat.blt_eq]; exact h0
  have e2 : Nat.beq (length (d ++ m)) (Nat.add d.length d.length) = true :=
    (nat_beq_iff _ _).mpr (by show (d ++ m).length = d.length + d.length; rw [List.length_append, hm])
  have e3 : Nat.beq (length m) d.length = true := (nat_beq_iff _ _).mpr hm
  unfold decodePtrBytesNoForge thinDecode
  simp only [e1, e2, e3, take_append, drop_append]
  cases decodeLittleEndianBits m <;> rfl

/-- **Exact wide slice/`str` encoding correspondence.** MiniRust `encodeWidePtrM .ElementCount`
produces the exact projection of `encodePtrBytes addr 8 a t ++ encodePlainLittleEndianBytes len 8`. -/
theorem encodeWidePtrM_slice_proj {M : Type} [Gen.Memory M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (addr len a t : Nat)
    (ha : addr < 2 ^ 64) (hl : len < 2 ^ 64) :
    Interp.encodeWidePtrM (M := M) .ElementCount
      { thin_pointer := { addr := (addr : Int), provenance := some (pv a t) },
        metadata := some (.ElementCount (len : Int)) } =
      .ok (projBytes pv (encodePtrBytes addr 8 a t ++ encodePlainLittleEndianBytes len 8)) := by
  rw [encodeWidePtrM_slice_eq addr len (some (pv a t)) ha hl]
  unfold projBytes
  rw [List.map_append]
  change Except.ok _ = Except.ok (projBytes pv (encodePtrBytes addr 8 a t) ++
    projBytes pv (encodePlainLittleEndianBytes len 8))
  rw [proj_encodePtrBytes (M := M) pv addr 8 a t, proj_plain_bytes (M := M) pv 8 len 0]

/-- **Exact wide `&dyn Trait` encoding correspondence.** MiniRust `encodeWidePtrM (.VTablePointer tr)`
produces the exact projection of `encodePtrBytes addr 8 a t ++ encodePtrBytes vtAddr 8 va vt`. -/
theorem encodeWidePtrM_dyn_proj {M : Type} [Gen.Memory M] (tr : Gen.TraitName)
    (pv : Nat → Nat → Gen.Memory.Provenance M) (addr vtAddr a t va vt : Nat)
    (ha : addr < 2 ^ 64) (hv : vtAddr < 2 ^ 64) :
    Interp.encodeWidePtrM (M := M) (.VTablePointer tr)
      { thin_pointer := { addr := (addr : Int), provenance := some (pv a t) },
        metadata := some (.VTablePointer { addr := (vtAddr : Int), provenance := some (pv va vt) }) } =
      .ok (projBytes pv (encodePtrBytes addr 8 a t ++ encodePtrBytes vtAddr 8 va vt)) := by
  rw [encodeWidePtrM_dyn_eq tr addr vtAddr (some (pv a t)) (some (pv va vt)) ha hv]
  unfold projBytes
  rw [List.map_append]
  change Except.ok _ = Except.ok (projBytes pv (encodePtrBytes addr 8 a t) ++
    projBytes pv (encodePtrBytes vtAddr 8 va vt))
  rw [proj_encodePtrBytes (M := M) pv addr 8 a t, proj_encodePtrBytes (M := M) pv vtAddr 8 va vt]

/-- **Universal wide slice/`str` decode correspondence.** On any 8-byte coherent data half `d` and
8-byte initialized provenance-free metadata half `m`, `Trusted` (`decodePtrBytesNoForge` for both
`.slice elem` and `.str`) and MiniRust (`Interp.decodeWidePtrM .ElementCount`) decode identically. -/
theorem coherent_wide_slice_decode_agreement {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (isRef : Bool) (elem : RigidTy)
    (d m : List AbstractByte) (f : PtrByteFrag) (md : List UInt8)
    (hd : d.length = 8) (hm : m.length = 8)
    (hcoh : abstractBytesCoherentPtrProv? d = some f) (hw : f.ptrBytes = 8)
    (hmd : trData m = some md) (hplain : abstractBytesHaveProv m = false) :
    ∃ dd, trData d = some dd ∧
      decodePtrBytesNoForge isRef (.slice elem) 8 (d ++ m) =
        some (.aggregate 0 [.ptr { allocId := f.allocId, offsetBytes := Interp.leValue dd } 8,
          .scalar ⟨Interp.leValue md, 8⟩]) ∧
      decodePtrBytesNoForge isRef .str 8 (d ++ m) =
        some (.aggregate 0 [.ptr { allocId := f.allocId, offsetBytes := Interp.leValue dd } 8,
          .scalar ⟨Interp.leValue md, 8⟩]) ∧
      Interp.decodeWidePtrM (M := M) .ElementCount (projBytes pv (d ++ m)) =
        .ok (some (.Ptr {
          thin_pointer := { addr := ((Interp.leValue dd : Nat) : Int),
                            provenance := some (pv f.allocId f.tag) },
          metadata := some (.ElementCount ((Interp.leValue md : Nat) : Int)) })) := by
  obtain ⟨dd, hdd, hthin, _⟩ := coherent_decode_agreement (M := M) pv d f isRef hd hcoh hw
  have hmbits : decodeLittleEndianBits m = some (Interp.leValue md) := by
    rw [bits_eq_leValue, hmd]; rfl
  have hmeta : sliceMetaDecode 8 m = some (.scalar ⟨Interp.leValue md, 8⟩) := by
    unfold sliceMetaDecode; rw [hmbits, hplain]
  have hproj : projBytes pv (d ++ m) = projBytes pv d ++ projBytes pv m := List.map_append
  refine ⟨dd, hdd, ?_, ?_, ?_⟩
  · have h := decodePtrBytesNoForge_slice isRef elem d m (by omega) (by omega)
    rw [hd] at h; rw [h, hthin, hmeta]
  · have h := decodePtrBytesNoForge_str isRef d m (by omega) (by omega)
    rw [hd] at h; rw [h, hthin, hmeta]
  · rw [hproj, decodeWidePtrM_slice_eq _ _ (by rw [projBytes_length, hd]) (by rw [projBytes_length, hm]),
      proj_data, proj_data, hdd, hmd, trusted_coherent_implies_minirust_retains pv d f hcoh]

/-- **Universal wide `&dyn Trait` decode correspondence.** On any 8-byte coherent data half `d` and
8-byte coherent vtable half `m`, `Trusted` (`decodePtrBytesNoForge`) and MiniRust
(`Interp.decodeWidePtrM (.VTablePointer trId)`) decode identically. -/
theorem coherent_wide_dyn_decode_agreement {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (isRef : Bool) (tr : String) (trId : Gen.TraitName)
    (d m : List AbstractByte) (fd fm : PtrByteFrag)
    (hd : d.length = 8) (hm : m.length = 8)
    (hcd : abstractBytesCoherentPtrProv? d = some fd) (hwd : fd.ptrBytes = 8)
    (hcm : abstractBytesCoherentPtrProv? m = some fm) (hwm : fm.ptrBytes = 8) :
    ∃ dd md, trData d = some dd ∧ trData m = some md ∧
      decodePtrBytesNoForge isRef (.dynamic tr) 8 (d ++ m) =
        some (.aggregate 0 [.ptr { allocId := fd.allocId, offsetBytes := Interp.leValue dd } 8,
          .ptr { allocId := fm.allocId, offsetBytes := Interp.leValue md } 8]) ∧
      Interp.decodeWidePtrM (M := M) (.VTablePointer trId) (projBytes pv (d ++ m)) =
        .ok (some (.Ptr {
          thin_pointer := { addr := ((Interp.leValue dd : Nat) : Int),
                            provenance := some (pv fd.allocId fd.tag) },
          metadata := some (.VTablePointer {
            addr := ((Interp.leValue md : Nat) : Int),
            provenance := some (pv fm.allocId fm.tag) }) })) := by
  obtain ⟨dd, hdd, htd, _⟩ := coherent_decode_agreement (M := M) pv d fd isRef hd hcd hwd
  obtain ⟨md, hmd, htm, _⟩ := coherent_decode_agreement (M := M) pv m fm isRef hm hcm hwm
  have hproj : projBytes pv (d ++ m) = projBytes pv d ++ projBytes pv m := List.map_append
  refine ⟨dd, md, hdd, hmd, ?_, ?_⟩
  · have h := decodePtrBytesNoForge_dyn isRef tr d m (by omega) (by omega)
    rw [hd] at h; rw [h, htd, htm]
  · rw [hproj, decodeWidePtrM_dyn_eq trId _ _ (by rw [projBytes_length, hd]) (by rw [projBytes_length, hm]),
      proj_data, proj_data, hdd, hmd,
      trusted_coherent_implies_minirust_retains pv d fd hcd,
      trusted_coherent_implies_minirust_retains pv m fm hcm]

/-- **Universal swapped wide-slice divergence (`DIV-MR-PTR2INT`).** On `m ++ d` where `m` is an
8-byte plain integer and `d` is an 8-byte coherent pointer, `Trusted` rejects `m ++ d` under
`Ptr2IntTransmutePolicy.strictUcg630Ub` (`= none`), whereas MiniRust `decodeWidePtrM .ElementCount`
accepts it as a provenance-free data pointer with element count equal to `d`'s address. -/
theorem swapped_wide_slice_div {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (isRef : Bool) (elem : RigidTy)
    (m d : List AbstractByte) (f : PtrByteFrag) (md : List UInt8)
    (hm : m.length = 8) (hd : d.length = 8)
    (hmd : trData m = some md) (hm0 : ∃ v, m[0]? = some (.init v none))
    (hcd : abstractBytesCoherentPtrProv? d = some f) :
    ∃ dd, trData d = some dd ∧
      decodePtrBytesNoForge isRef (.slice elem) 8 (m ++ d) = none ∧
      Interp.decodeWidePtrM (M := M) .ElementCount (projBytes pv (m ++ d)) =
        .ok (some (.Ptr {
          thin_pointer := { addr := ((Interp.leValue md : Nat) : Int), provenance := none },
          metadata := some (.ElementCount ((Interp.leValue dd : Nat) : Int)) })) := by
  obtain ⟨_, _, hcoh⟩ := (coherent?_eq_some_iff d f).mp hcd
  obtain ⟨dd, hdd⟩ := trCoh_data _ _ _ _ d 0 hcoh
  have hdp : abstractBytesHaveProv d = true := by
    cases d with
    | nil => cases hd
    | cons x rest =>
      obtain ⟨v, rfl⟩ := hcoh.1
      rfl
  obtain ⟨v0, hv0⟩ := hm0
  have hmp : mrProvM M (projBytes pv m) = none := missing_provenance_strips_minirust pv m 0 v0 hv0
  have hproj : projBytes pv (m ++ d) = projBytes pv m ++ projBytes pv d := List.map_append
  refine ⟨dd, hdd, ?_, ?_⟩
  · have h := slice_meta_with_provenance_rejected isRef elem m d (by omega) (by omega) hdp
    rw [hm] at h; exact h
  · rw [hproj, decodeWidePtrM_slice_eq _ _ (by rw [projBytes_length, hm]) (by rw [projBytes_length, hd]),
      proj_data, proj_data, hmd, hdd, hmp]

/-! ### §9. `Kani#5205`: read-time validity of untyped bytes -/

/-- **MiniRust rejects every non-`0`/`1` byte at `Type::Bool`** (for any
fragment the byte may carry). -/
theorem minirust_bool_invalid (v : UInt8) (fr : Option (Gen.ProvenanceFrag Interp.Prov))
    (h0 : v ≠ 0) (h1 : v ≠ 1) :
    Interp.Type.decode .Bool [.Init v fr] = .ok none := by
  rw [Interp.Type.decode]
  · rfl
  · intro x h
    injection h with h _
    injection h with hv _
    exact h0 hv
  · intro x h
    injection h with h _
    injection h with hv _
    exact h1 hv

/-- **MiniRust accepts every initialized byte at `Type::Int(u8)`**: an invalid
`bool` bit pattern is representable as an untyped byte. -/
theorem minirust_u8_valid (v : UInt8) (fr : Option (Gen.ProvenanceFrag Interp.Prov)) :
    Interp.Type.decode (.Int ⟨.Unsigned, ⟨1⟩⟩) [.Init v fr] = .ok (some (.Int (v.toNat : Int))) := by
  rw [Interp.Type.decode]
  rfl

/-- **Universal polymorphic `Kani#5205` `Trusted` ↔ MiniRust `bool` validity correspondence**
across BOTH `BasicMemory` and `TreeBorrowsMemory` for every byte `v : UInt8`: untyped storage
accepts `v`, while typed `bool` decoding / validation agrees iff `v ∈ {0, 1}`. -/
theorem kani5205_bool_correspondence_M {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (layouts : LayoutTable) (tyBool : Ty)
    (hty : tyBool.kind = .bool) (v : UInt8) :
    decodeUntypedStorageBytes defaultCodecFuel layouts tyBool [.init v none] =
      some (.scalar ⟨v.toNat, 1⟩) ∧
    ((decodeTypedValueFromBytes defaultCodecFuel layouts tyBool [.init v none]).isSome = true ↔
      ∃ b, Interp.Type.decodeM (M := M) .Bool (projBytes pv [.init v none]) = .ok (some (.Bool b))) ∧
    (validateValueForTy? layouts (some tyBool) (.scalar ⟨v.toNat, 1⟩) = true ↔
      ∃ b, Interp.Type.decodeM (M := M) .Bool (projBytes pv [.init v none]) = .ok (some (.Bool b))) := by
  obtain ⟨kind, lidx⟩ := tyBool
  dsimp only at hty
  subst hty
  have hun : decodeUntypedStorageBytes defaultCodecFuel layouts ⟨.bool, lidx⟩ [.init v none] =
      some (.scalar ⟨v.toNat, 1⟩) := by
    show some (Value.scalar ⟨v.toBitVec.toNat + 256 * 0, 1⟩) = some (Value.scalar ⟨v.toNat, 1⟩)
    rw [Nat.mul_zero, Nat.add_zero]; rfl
  have hmr : Interp.Type.decodeM (M := M) .Bool (projBytes pv [.init v none]) =
      (if v = 0 then .ok (some (.Bool false))
       else if v = 1 then .ok (some (.Bool true))
       else .ok none) := minirust_bool_decodeM_iff (M := M) v none
  refine ⟨hun, ?_, ?_⟩
  · by_cases h0 : v = 0
    · subst h0
      have htr : decodeTypedValueFromBytes defaultCodecFuel layouts ⟨.bool, lidx⟩ [.init 0 none] =
          some (.scalar ⟨0, 1⟩) := rfl
      simp [hmr, htr]
    · by_cases h1 : v = 1
      · subst h1
        have htr : decodeTypedValueFromBytes defaultCodecFuel layouts ⟨.bool, lidx⟩ [.init 1 none] =
            some (.scalar ⟨1, 1⟩) := rfl
        simp [hmr, htr]
      · have hne0 : Nat.beq v.toBitVec.toNat 0 = false := by
          cases h : Nat.beq v.toBitVec.toNat 0 with
          | false => rfl
          | true =>
            have hv0 : v.toNat = 0 := (nat_beq_iff _ _).mp h
            exact absurd (UInt8.toNat_inj.mp hv0) h0
        have hne1 : Nat.beq v.toBitVec.toNat 1 = false := by
          cases h : Nat.beq v.toBitVec.toNat 1 with
          | false => rfl
          | true =>
            have hv1 : v.toNat = 1 := (nat_beq_iff _ _).mp h
            exact absurd (UInt8.toNat_inj.mp hv1) h1
        have htr : decodeTypedValueFromBytes defaultCodecFuel layouts ⟨.bool, lidx⟩ [.init v none] = none := by
          show (match Nat.beq v.toBitVec.toNat 0 with
            | true => some (Value.scalar ⟨0, 1⟩)
            | false => match Nat.beq v.toBitVec.toNat 1 with
              | true => some (Value.scalar ⟨1, 1⟩)
              | false => none) = none
          rw [hne0, hne1]
        simp [hmr, h0, h1, htr]
  · by_cases h0 : v = 0
    · subst h0
      have hval : validateValueForTy? layouts (some ⟨.bool, lidx⟩) (.scalar ⟨0, 1⟩) = true := rfl
      simp [hmr, hval]
    · by_cases h1 : v = 1
      · subst h1
        have hval : validateValueForTy? layouts (some ⟨.bool, lidx⟩) (.scalar ⟨1, 1⟩) = true := rfl
        simp [hmr, hval]
      · have hble : Nat.ble v.toNat 1 = false := by
          cases h : Nat.ble v.toNat 1 with
          | false => rfl
          | true =>
            have hle : v.toNat ≤ 1 := Nat.ble_eq.mp h
            have : v.toNat = 0 ∨ v.toNat = 1 := by omega
            rcases this with hv | hv
            · exact absurd (UInt8.toNat_inj.mp hv) h0
            · exact absurd (UInt8.toNat_inj.mp hv) h1
        have hval : validateValueForTy? layouts (some ⟨.bool, lidx⟩) (.scalar ⟨v.toNat, 1⟩) = false := by
          show Bool.and true (Nat.ble v.toNat 1) = false
          rw [hble]; rfl
        simp [hmr, h0, h1, hval]

/-! ### §10. Fixtures and kernel-checked witnesses -/

section Witnesses

open Trusted.Rustc.V2026_08_01.Layout

/-- `p = alloc 7 + 0x1000`. -/
def wP : List AbstractByte := encodePtrBytes 0x1000 8 7 7
/-- `p + 4`. -/
def wP4 : List AbstractByte := encodePtrBytes 0x1004 8 7 7
/-- `p + 256`: byte 0 is `0x00`, exactly as in `p`. -/
def wP256 : List AbstractByte := encodePtrBytes 0x1100 8 7 7
/-- The all-zero pointer image `alloc 7 + 0`. -/
def wZero : List AbstractByte := encodePtrBytes 0 8 7 7
/-- A pointer into another allocation. -/
def wOther : List AbstractByte := encodePtrBytes 0x1000 8 8 8
/-- The same allocation under another borrow tag. -/
def wOtherTag : List AbstractByte := encodePtrBytes 0x1000 8 7 9
/-- The plain integer `0x1000`. -/
def wPlain : List AbstractByte := encodePlainLittleEndianBytes 0x1000 8
/-- The plain slice length `3`. -/
def wLen3 : List AbstractByte := encodePlainLittleEndianBytes 3 8
/-- A vtable pointer `alloc 42 + 0x80`. -/
def wVt : List AbstractByte := encodePtrBytes 0x80 8 42 42

def wUnitL : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }
def wU8L : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wBoolL : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wCharL : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wU32L : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [wUnitL, wU8L, wBoolL, wCharL, wU32L] }
def wTyU8 : Ty := { kind := .uint .u8, layoutIdx := 1 }
def wTyBool : Ty := { kind := .bool, layoutIdx := 2 }
def wTyChar : Ty := { kind := .char, layoutIdx := 3 }
def wTyU32 : Ty := { kind := .uint .u32, layoutIdx := 4 }
/-- The little-endian bytes of the surrogate code point `0xD800`. -/
def wSurrogate : List AbstractByte :=
  [.init 0x00 none, .init 0xD8 none, .init 0x00 none, .init 0x00 none]

/-- **Round-trip witness (`alloc 7 + 0x1000`).** MiniRust `encode_ptr` produces
exactly the projected `Trusted` bytes, and both authorities decode them back to
the same pointer, across `BasicMemory` and `TreeBorrowsMemory`. -/
theorem w_roundtrip :
    Interp.encodePtr (⟨0x1000, some (bmProv 7 7)⟩ : Interp.Ptr) = .ok (projBytes bmProv wP) ∧
    Interp.encodePtrM (M := Interp.TBM) ⟨0x1000, some (tbProv 7 7)⟩ =
      .ok (projBytes tbProv wP) ∧
    Interp.decodePtr (projBytes bmProv wP) = .ok (some ⟨0x1000, some (bmProv 7 7)⟩) ∧
    Interp.decodePtrM (M := Interp.BM) (projBytes bmProv wP) =
      .ok (some ⟨0x1000, some (bmProv 7 7)⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv wP) =
      .ok (some ⟨0x1000, some (tbProv 7 7)⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 wP = some (.ptr ⟨7, 0x1000⟩ 8) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 wP = some (.ptr ⟨7, 0x1000⟩ 8) ∧
    decodeScalarLayoutBytesNoForge (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩) wP =
      some (.ptr ⟨7, 0x1000⟩ 8) ∧
    encodeUntypedValueToBytes 1 (.ptr ⟨7, 0x1000⟩ 8) = some wP ∧
    decodeRawAbstractByteVals? (wP.map encodeRawAbstractByteVal) = some wP := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **`UCG#558` W1 witnesses.** Full reversal (of the all-zero image of offset
`0`, and of `p`), the byte-0/byte-1 swap, and byte 0 repeated 8×: `Trusted`
reads a raw pointer as a plain integer and rejects a reference; MiniRust reads a
pointer without provenance. -/
theorem w_ucg558_w1 :
    decodePtrBytesNoForge false (.uint .u8) 8 wZero.reverse = some (.scalar ⟨0, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 wZero.reverse = none ∧
    Interp.decodePtr (projBytes bmProv wZero.reverse) = .ok (some ⟨0, none⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv wZero.reverse) = .ok (some ⟨0, none⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 wP.reverse = some (.scalar ⟨0x10000000000000, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 wP.reverse = none ∧
    Interp.decodePtr (projBytes bmProv wP.reverse) = .ok (some ⟨0x10000000000000, none⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 (swap01 wP) = some (.scalar ⟨0x10, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 (swap01 wP) = none ∧
    Interp.decodePtr (projBytes bmProv (swap01 wP)) = .ok (some ⟨0x10, none⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (swap01 wP)) = .ok (some ⟨0x10, none⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 (dupHead wP) = some (.scalar ⟨0, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 (dupHead wP) = none ∧
    Interp.decodePtr (projBytes bmProv (dupHead wP)) = .ok (some ⟨0, none⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (dupHead wP)) = .ok (some ⟨0, none⟩) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **Mixed / missing provenance and uninitialized bytes.** A cross-allocation
splice, one provenance byte followed by seven plain bytes, an all-plain integer
image (no integer-to-pointer forging), and a stream with one `.uninit` byte. -/
theorem w_mixed_missing_uninit :
    decodePtrBytesNoForge false (.uint .u8) 8 (wP.take 4 ++ wOther.drop 4) =
      some (.scalar ⟨0x1000, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 (wP.take 4 ++ wOther.drop 4) = none ∧
    Interp.decodePtr (projBytes bmProv (wP.take 4 ++ wOther.drop 4)) =
      .ok (some ⟨0x1000, none⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (wP.take 4 ++ wOther.drop 4)) =
      .ok (some ⟨0x1000, none⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 (wP.take 1 ++ wPlain.drop 1) =
      some (.scalar ⟨0x1000, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 (wP.take 1 ++ wPlain.drop 1) = none ∧
    Interp.decodePtr (projBytes bmProv (wP.take 1 ++ wPlain.drop 1)) =
      .ok (some ⟨0x1000, none⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 wPlain = some (.scalar ⟨0x1000, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 wPlain = none ∧
    Interp.decodePtr (projBytes bmProv wPlain) = .ok (some ⟨0x1000, none⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv wPlain) = .ok (some ⟨0x1000, none⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 (wP.take 7 ++ [.uninit]) = none ∧
    decodePtrBytesNoForge true (.uint .u8) 8 (wP.take 7 ++ [.uninit]) = none ∧
    Interp.decodePtr (projBytes bmProv (wP.take 7 ++ [.uninit])) = .ok none ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (wP.take 7 ++ [.uninit])) = .ok none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **`DIV-MR-OFFSET-SPLICE`: the `p` / `p + 4` splice.** Vendored MiniRust
retains the provenance and reads the pointer `alloc 7 + 0x1000`; `Trusted`
strips it (a raw pointer becomes the integer `0x1000`, a reference is invalid). -/
theorem w_offset_splice_p_p4 :
    Interp.decodePtr (projBytes bmProv (wP.take 4 ++ wP4.drop 4)) =
      .ok (some ⟨0x1000, some (bmProv 7 7)⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (wP.take 4 ++ wP4.drop 4)) =
      .ok (some ⟨0x1000, some (tbProv 7 7)⟩) ∧
    Interp.decodePtrProvenance 0 (Interp.firstProvenance (projBytes bmProv (wP.take 4 ++ wP4.drop 4)))
      (projBytes bmProv (wP.take 4 ++ wP4.drop 4)) = some (bmProv 7 7) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 (wP.take 4 ++ wP4.drop 4) =
      some (.scalar ⟨0x1000, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 (wP.take 4 ++ wP4.drop 4) = none ∧
    decodePtrBytesNoForge true (.fnPtr [] (.tuple []) .safe .rust) 8 (wP.take 4 ++ wP4.drop 4) =
      none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **`DIV-MR-OFFSET-SPLICE`: the `p` / `p + 256` splice.** Byte 0 is `0x00` in
both pointers, so the spliced byte *values* are exactly those of `p + 256`;
only the fragment's originating offset tells the bytes apart. MiniRust retains
the provenance; `Trusted` strips it. -/
theorem w_offset_splice_p_p256 :
    wP[0]? = some (.init 0x00 (some ⟨7, 7, 0, 0x1000, 8⟩)) ∧
    wP256[0]? = some (.init 0x00 (some ⟨7, 7, 0, 0x1100, 8⟩)) ∧
    Interp.decodePtr (projBytes bmProv (wP.take 1 ++ wP256.drop 1)) =
      .ok (some ⟨0x1100, some (bmProv 7 7)⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (wP.take 1 ++ wP256.drop 1)) =
      .ok (some ⟨0x1100, some (tbProv 7 7)⟩) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 (wP.take 1 ++ wP256.drop 1) =
      some (.scalar ⟨0x1100, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 (wP.take 1 ++ wP256.drop 1) = none ∧
    decodePtrBytesNoForge false (.uint .u8) 8 wP256 = some (.ptr ⟨7, 0x1100⟩ 8) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **`DIV-MR-BASIC-TAG`.** A splice of two pointers into one allocation under
different borrow tags: `Trusted` and `TreeBorrowsMemory` strip the provenance,
while tag-blind `BasicMemory` retains it. -/
theorem w_basic_memory_tag_blind :
    decodePtrBytesNoForge false (.uint .u8) 8 (wP.take 4 ++ wOtherTag.drop 4) =
      some (.scalar ⟨0x1000, 8⟩) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (wP.take 4 ++ wOtherTag.drop 4)) =
      .ok (some ⟨0x1000, none⟩) ∧
    Interp.decodePtr (projBytes bmProv (wP.take 4 ++ wOtherTag.drop 4)) =
      .ok (some ⟨0x1000, some (bmProv 7 7)⟩) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **Wide slice pointers** (`&[u8]`, `*const [u8]`, `&str`): the intact
`data ++ len` image decodes identically in both authorities. -/
theorem w_wide_slice :
    decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (wP ++ wLen3) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨3, 8⟩]) ∧
    decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (wP ++ wLen3) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨3, 8⟩]) ∧
    decodePtrBytesNoForge true .str 8 (wP ++ wLen3) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨3, 8⟩]) ∧
    Interp.decodeWidePtr .ElementCount (projBytes bmProv (wP ++ wLen3)) =
      .ok (some (.Ptr ⟨⟨0x1000, some (bmProv 7 7)⟩, some (.ElementCount 3)⟩)) ∧
    Interp.decodeWidePtrM (M := Interp.TBM) .ElementCount (projBytes tbProv (wP ++ wLen3)) =
      .ok (some (.Ptr ⟨⟨0x1000, some (tbProv 7 7)⟩, some (.ElementCount 3)⟩)) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **Swapped halves (`DIV-MR-PTR2INT`).** For `len ++ data`, `Trusted` rejects
the provenance-bearing length half (for `&[u8]`, `*const [u8]`, and `&str`);
MiniRust decodes the "length" at `Type::Int`, which ignores provenance, and
yields a provenance-free data pointer `3` with element count `0x1000`. A
reversed data half is stripped by both. -/
theorem w_wide_swapped_halves :
    decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (wLen3 ++ wP) = none ∧
    decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (wLen3 ++ wP) = none ∧
    decodePtrBytesNoForge true .str 8 (wLen3 ++ wP) = none ∧
    Interp.decodeWidePtr .ElementCount (projBytes bmProv (wLen3 ++ wP)) =
      .ok (some (.Ptr ⟨⟨3, none⟩, some (.ElementCount 0x1000)⟩)) ∧
    Interp.decodeWidePtrM (M := Interp.TBM) .ElementCount (projBytes tbProv (wLen3 ++ wP)) =
      .ok (some (.Ptr ⟨⟨3, none⟩, some (.ElementCount 0x1000)⟩)) ∧
    decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (wP.reverse ++ wLen3) = none ∧
    decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (wP.reverse ++ wLen3) =
      some (.aggregate 0 [.scalar ⟨0x10000000000000, 8⟩, .scalar ⟨3, 8⟩]) ∧
    Interp.decodeWidePtr .ElementCount (projBytes bmProv (wP.reverse ++ wLen3)) =
      .ok (some (.Ptr ⟨⟨0x10000000000000, none⟩, some (.ElementCount 3)⟩)) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **Trait-object pointers (`&dyn Trait`, `DIV-MR-DYN-VTABLE`).** The intact
`data ++ vtable` image decodes identically; with a reversed vtable half
`Trusted` rejects `&dyn Trait` at decode time (and reads `*const dyn Trait` as a
data pointer with an integer), while MiniRust decodes a provenance-free vtable
pointer that only `check_value` rejects. -/
theorem w_wide_dyn :
    decodePtrBytesNoForge true (.dynamic "T") 8 (wP ++ wVt) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .ptr ⟨42, 0x80⟩ 8]) ∧
    Interp.decodeWidePtr (.VTablePointer ⟨⟨0⟩⟩) (projBytes bmProv (wP ++ wVt)) =
      .ok (some (.Ptr ⟨⟨0x1000, some (bmProv 7 7)⟩,
        some (.VTablePointer ⟨0x80, some (bmProv 42 42)⟩)⟩)) ∧
    Interp.decodeWidePtrM (M := Interp.TBM) (.VTablePointer ⟨⟨0⟩⟩) (projBytes tbProv (wP ++ wVt)) =
      .ok (some (.Ptr ⟨⟨0x1000, some (tbProv 7 7)⟩,
        some (.VTablePointer ⟨0x80, some (tbProv 42 42)⟩)⟩)) ∧
    decodePtrBytesNoForge true (.dynamic "T") 8 (wP ++ wVt.reverse) = none ∧
    decodePtrBytesNoForge false (.dynamic "T") 8 (wP ++ wVt.reverse) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨0x8000000000000000, 8⟩]) ∧
    Interp.decodeWidePtr (.VTablePointer ⟨⟨0⟩⟩) (projBytes bmProv (wP ++ wVt.reverse)) =
      .ok (some (.Ptr ⟨⟨0x1000, some (bmProv 7 7)⟩,
        some (.VTablePointer ⟨0x8000000000000000, none⟩)⟩)) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **`Kani#5205`, `2u8` as `bool`.** The byte `2` is representable as an untyped
byte in both authorities (`u8`, the raw-byte carrier, MiniRust `Type::Int(u8)`
and `[u8; 1]`) — writing it is not UB — and is rejected by the typed `bool`
decode of both authorities (`Trusted`: `none`, the `.ub` read fault; MiniRust:
`None`). -/
theorem w_kani5205_bool :
    encodeUntypedValueToBytes 1 (.scalar ⟨2, 1⟩) = some [.init 2 none] ∧
    encodeValueToBytes defaultCodecFuel wLayouts wTyU8 (.scalar ⟨2, 1⟩) = some [.init 2 none] ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyU8 [.init 2 none] =
      some (.scalar ⟨2, 1⟩) ∧
    decodeRawAbstractByteVals? [encodeRawAbstractByteVal (.init 2 none)] = some [.init 2 none] ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyBool [.init 2 none] = none ∧
    validateValueForTy? wLayouts (some wTyBool) (.scalar ⟨2, 1⟩) = false ∧
    validateValueForTy? wLayouts (some wTyU8) (.scalar ⟨2, 1⟩) = true ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyBool [.init 1 none] =
      some (.scalar ⟨1, 1⟩) ∧
    Interp.Type.decode (.Int ⟨.Unsigned, ⟨1⟩⟩) (projBytes bmProv [.init 2 none]) =
      .ok (some (.Int 2)) ∧
    Interp.Type.decode .Bool (projBytes bmProv [.init 2 none]) = .ok none ∧
    Interp.Type.decode .Bool (projBytes bmProv [.init 1 none]) = .ok (some (.Bool true)) ∧
    Interp.Type.decodeM (M := Interp.TBM) (.Int ⟨.Unsigned, ⟨1⟩⟩) (projBytes tbProv [.init 2 none]) =
      .ok (some (.Int 2)) ∧
    Interp.Type.decodeM (M := Interp.TBM) .Bool (projBytes tbProv [.init 2 none]) = .ok none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- **`Kani#5205`, `0xD800` as `char` (`DIV-MR-CHAR`).** The surrogate bit
pattern is representable as untyped bytes (`u32`, MiniRust `Type::Int(u32)`) and
is rejected by the `Trusted` typed `char` decode. MiniRust has no `char` type:
its closest type, `Type::Int(u32)`, accepts the pattern. -/
theorem w_kani5205_char :
    encodeUntypedValueToBytes 1 (.scalar ⟨0xD800, 4⟩) = some wSurrogate ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyU32 wSurrogate =
      some (.scalar ⟨0xD800, 4⟩) ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyChar wSurrogate = none ∧
    validateValueForTy? wLayouts (some wTyChar) (.scalar ⟨0xD800, 4⟩) = false ∧
    validateValueForTy? wLayouts (some wTyU32) (.scalar ⟨0xD800, 4⟩) = true ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyChar
      [.init 0x41 none, .init 0 none, .init 0 none, .init 0 none] = some (.scalar ⟨0x41, 4⟩) ∧
    Interp.Type.decode (.Int ⟨.Unsigned, ⟨4⟩⟩) (projBytes bmProv wSurrogate) =
      .ok (some (.Int 0xD800)) ∧
    Interp.Type.decodeM (M := Interp.TBM) (.Int ⟨.Unsigned, ⟨4⟩⟩) (projBytes tbProv wSurrogate) =
      .ok (some (.Int 0xD800)) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-! ### §11. Non-vacuous instantiations of the universal theorems -/

theorem coherent_decode_agreement_instance :
    (∃ data, trData wP = some data ∧
      thinDecode true 8 wP = some (.ptr { allocId := 7, offsetBytes := Interp.leValue data } 8) ∧
      Interp.decodePtrM (M := Interp.BM) (projBytes bmProv wP) =
        .ok (some { addr := ((Interp.leValue data : Nat) : Int),
                    provenance := some (bmProv 7 7) })) ∧
    (∃ data, trData wP = some data ∧
      thinDecode false 8 wP = some (.ptr { allocId := 7, offsetBytes := Interp.leValue data } 8) ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv wP) =
        .ok (some { addr := ((Interp.leValue data : Nat) : Int),
                    provenance := some (tbProv 7 7) })) :=
  ⟨coherent_decode_agreement (M := Interp.BM) bmProv wP ⟨7, 7, 0, 0x1000, 8⟩ true rfl rfl rfl,
   coherent_decode_agreement (M := Interp.TBM) tbProv wP ⟨7, 7, 0, 0x1000, 8⟩ false rfl rfl rfl⟩

theorem encode_roundtrip_instance :
    Interp.encodePtrM (M := Interp.TBM) { addr := ((0x1000 : Nat) : Int), provenance := some (tbProv 7 7) } =
      .ok (projBytes tbProv (encodePtrBytes 0x1000 8 7 7)) ∧
    Interp.encodePtr { addr := ((0x1000 : Nat) : Int), provenance := some (bmProv 7 7) } =
      .ok (projBytes bmProv (encodePtrBytes 0x1000 8 7 7)) ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (encodePtrBytes 0x1000 8 7 7)) =
      .ok (some { addr := ((0x1000 : Nat) : Int), provenance := some (tbProv 7 7) }) ∧
    thinDecode true 8 (encodePtrBytes 0x1000 8 7 7) =
      some (.ptr { allocId := 7, offsetBytes := 0x1000 % 256 ^ 8 } 8) ∧
    thinDecode false 4 (encodePtrBytes 0x1000 4 9 9) =
      some (.ptr { allocId := 9, offsetBytes := 0x1000 % 256 ^ 4 } 4) :=
  ⟨encodePtrM_proj tbProv 0x1000 7 7 (by decide), encodePtr_proj 0x1000 7 7 (by decide),
   decodePtrM_proj_encodePtrBytes tbProv 0x1000 7 7 (by decide),
   thinDecode_encodePtrBytes true 0x1000 8 7 7 (by decide),
   thinDecode_encodePtrBytes false 0x1000 4 9 9 (by decide)⟩

theorem rawCarrier_ptr_roundtrip_instance :
    ∃ bs, decodeRawAbstractByteVals? (wP.map encodeRawAbstractByteVal) = some bs ∧
      thinDecode true 8 bs = some (.ptr { allocId := 7, offsetBytes := 0x1000 } 8) ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv bs) =
        .ok (some { addr := ((0x1000 : Nat) : Int), provenance := some (tbProv 7 7) }) :=
  rawCarrier_ptr_roundtrip (M := Interp.TBM) tbProv true 0x1000 7 7 (by decide)

theorem strip_laws_instance :
    (abstractBytesCoherentPtrProv? wZero.reverse = none ∧
      mrProvM Interp.BM (projBytes bmProv wZero.reverse) = none) ∧
    (abstractBytesCoherentPtrProv? (swap01 wP) = none ∧
      mrProvM Interp.TBM (projBytes tbProv (swap01 wP)) = none) ∧
    (abstractBytesCoherentPtrProv? (dupHead wP) = none ∧
      mrProvM Interp.TBM (projBytes tbProv (dupHead wP)) = none) ∧
    abstractBytesCoherentPtrProv? (wP.take 4 ++ wOther.drop 4) = none ∧
    mrProvM Interp.BM (projBytes bmProv (wP.take 4 ++ wOther.drop 4)) = none ∧
    abstractBytesCoherentPtrProv? wPlain = none ∧
    mrProvM Interp.TBM (projBytes tbProv wPlain) = none ∧
    thinDecode true 8 (wP.take 7 ++ [.uninit]) = none ∧
    Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (wP.take 7 ++ [.uninit])) = .ok none :=
  ⟨reversal_strips bmProv 0 7 7, swap01_strips tbProv 0x1000 7 7, dupHead_strips tbProv 0x1000 7 7,
   mixed_provenance_strips_trusted _ 0 4 _ _ ⟨7, 7, 0, 0x1000, 8⟩ ⟨8, 8, 4, 0x1000, 8⟩ rfl rfl
     (Or.inl (by decide)),
   mixed_provenance_strips_minirust (M := Interp.BM) bmProv _ 0 4 _ _ ⟨7, 7, 0, 0x1000, 8⟩
     ⟨8, 8, 4, 0x1000, 8⟩ rfl rfl (by decide),
   missing_provenance_strips_trusted wPlain 0 _ rfl,
   missing_provenance_strips_minirust (M := Interp.TBM) tbProv wPlain 0 _ rfl,
   uninit_rejected_trusted true 8 _ (List.mem_append_right _ (List.Mem.head _)),
   uninit_rejected_minirust (M := Interp.TBM) tbProv _ rfl
     (List.mem_append_right _ (List.Mem.head _))⟩

/-- The `p` / `p + 4` and `p` / `p + 256` splices instantiate both halves of the
strict refinement, and `converse_gap_iff` on a non-degenerate stream. -/
theorem offset_splice_instance :
    abstractBytesCoherentPtrProv? (wP.take 4 ++ wP4.drop 4) = none ∧
    mrProvM Interp.TBM (projBytes tbProv (wP.take 4 ++ wP4.drop 4)) = some (tbProv 7 7) ∧
    abstractBytesCoherentPtrProv? (wP.take 1 ++ wP256.drop 1) = none ∧
    mrProvM Interp.BM (projBytes bmProv (wP.take 1 ++ wP256.drop 1)) = some (bmProv 7 7) ∧
    (abstractBytesCoherentPtrProv? (wP.take 1 ++ wP256.drop 1) = none ↔
      ∃ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
        (wP.take 1 ++ wP256.drop 1)[i]? = some (.init vi (some fi)) ∧
        (wP.take 1 ++ wP256.drop 1)[j]? = some (.init vj (some fj)) ∧
        (fi.origOffset ≠ fj.origOffset ∨ fi.ptrBytes ≠ fj.ptrBytes ∨
          fi.ptrBytes ≠ (wP.take 1 ++ wP256.drop 1).length)) :=
  ⟨offset_splice_trusted_strips _ 0x1000 0x1004 8 7 7 0 4 _ _ rfl rfl rfl rfl (by decide),
   offset_splice_minirust_retains (M := Interp.TBM) tbProv _ 0x1000 0x1004 8 7 7
     (List.cons_ne_nil _ _) (by
       intro i b h
       match i, h with
       | 0, h => exact Or.inl h
       | 1, h => exact Or.inl h
       | 2, h => exact Or.inl h
       | 3, h => exact Or.inl h
       | 4, h => exact Or.inr h
       | 5, h => exact Or.inr h
       | 6, h => exact Or.inr h
       | 7, h => exact Or.inr h
       | _ + 8, h =>
         have h' : (none : Option AbstractByte) = some b := h
         cases h'),
   offset_splice_trusted_strips _ 0x1000 0x1100 8 7 7 0 1 _ _ rfl rfl rfl rfl (by decide),
   offset_splice_minirust_retains (M := Interp.BM) bmProv _ 0x1000 0x1100 8 7 7
     (List.cons_ne_nil _ _) (by
       intro i b h
       match i, h with
       | 0, h => exact Or.inl h
       | 1, h => exact Or.inr h
       | 2, h => exact Or.inr h
       | 3, h => exact Or.inr h
       | 4, h => exact Or.inr h
       | 5, h => exact Or.inr h
       | 6, h => exact Or.inr h
       | 7, h => exact Or.inr h
       | _ + 8, h =>
         have h' : (none : Option AbstractByte) = some b := h
         cases h'),
   converse_gap_iff (M := Interp.TBM) tbProv tbProv_inj _ (tbProv 7 7) rfl⟩

theorem wide_and_bool_instance :
    decodePtrBytesNoForge true (.slice (.uint .u8)) wLen3.length (wLen3 ++ wP) = none ∧
    decodePtrBytesNoForge false (.slice (.uint .u8)) wP.length (wP ++ wLen3) =
      (match thinDecode false wP.length wP, sliceMetaDecode wP.length wLen3 with
       | some dv, some mv => some (.aggregate 0 [dv, mv])
       | _, _ => none) ∧
    Interp.Type.decode .Bool [.Init 2 none] = .ok none ∧
    Interp.Type.decode (.Int ⟨.Unsigned, ⟨1⟩⟩) [.Init 2 none] = .ok (some (.Int ((2 : UInt8).toNat : Int))) :=
  ⟨slice_meta_with_provenance_rejected true (.uint .u8) wLen3 wP (by decide) rfl rfl,
   decodePtrBytesNoForge_slice false (.uint .u8) wP wLen3 (by decide) rfl,
   minirust_bool_invalid 2 none (by decide) (by decide), minirust_u8_valid 2 none⟩

def wUnalignedBoolL : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .arbitrary [⟨0⟩] [0], variants := .single 0, isUninhabited := false,
    fieldLayouts := [2] }
def wMaybeUninitBoolL : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [2, 0] }
def wKaniLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [wUnitL, wU8L, wBoolL, wCharL, wU32L, wUnalignedBoolL, wMaybeUninitBoolL] }
def wTyUnalignedBool : Ty := { kind := .adt "Unaligned" [.bool], layoutIdx := 5 }
def wTyMaybeUninitBool : Ty := { kind := .adt "core::mem::MaybeUninit" [.bool], layoutIdx := 6 }
def wTyRawPtrU8 : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }

/-- **`Kani#5205`: `Unaligned<bool>` and `MaybeUninit<bool>`** across `Trusted` and MiniRust
(`BasicMemory` and `TreeBorrowsMemory`). Untyped storage accepts `2u8` (including inside
`MaybeUninit<bool>` and MiniRust `Type::Union`); typed `Unaligned<bool>` / `bool` reads reject it
in both authorities. -/
theorem w_kani5205_unaligned_and_maybeuninit :
    decodeUntypedStorageBytes defaultCodecFuel wKaniLayouts wTyUnalignedBool [.init 2 none] =
      some (.aggregate 0 [.scalar ⟨2, 1⟩]) ∧
    decodeTypedValueFromBytes defaultCodecFuel wKaniLayouts wTyUnalignedBool [.init 2 none] = none ∧
    decodeTypedValueFromBytes defaultCodecFuel wKaniLayouts wTyUnalignedBool [.init 1 none] =
      some (.aggregate 0 [.scalar ⟨1, 1⟩]) ∧
    (decodeTypedValueFromBytes defaultCodecFuel wKaniLayouts wTyMaybeUninitBool [.init 2 none]).isSome = true ∧
    Interp.Type.decodeM (M := Interp.BM) (.Union [] [(⟨0⟩, ⟨1⟩)] ⟨1⟩ ⟨1⟩) [.Init 2 none] =
      .ok (some (.Union [[.Init 2 none]])) ∧
    Interp.Type.decodeM (M := Interp.TBM) (.Union [] [(⟨0⟩, ⟨1⟩)] ⟨1⟩ ⟨1⟩) [.Init 2 none] =
      .ok (some (.Union [[.Init 2 none]])) ∧
    Interp.Type.decodeM (M := Interp.BM) .Bool [.Init 2 none] = .ok none ∧
    Interp.Type.decodeM (M := Interp.TBM) .Bool [.Init 2 none] = .ok none ∧
    Interp.Type.decodeM (M := Interp.TBM) .Bool [.Uninit] = .ok none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- Complete non-vacuous instantiations of every universal `A0` and `ep2-B1` theorem in this
dialect: `scalarLayoutPtr_{coherent,incoherent,union_coherent,union_incoherent}`,
`scalarLayoutNonPtr_strictUb_rejects_prov`, `decodePtrBytesNoForge_{thin,str,dyn}`,
`encodeUntyped_ptr`, `encodeValueToBytes_thinPtr`, `proj_plain_bytes`,
`trusted_retains_implies_minirust_retains`, `thinDecode_{raw_incoherent,ref_incoherent,uninit}`,
`w1_transforms_decode_strips`, `offset_splice_decode_divergence`, `encodeWidePtrM_{slice,dyn}_proj`,
`coherent_wide_{slice,dyn}_decode_agreement`, `swapped_wide_slice_div`,
`kani5205_bool_correspondence_M`, and shared `*_eq_M` / `bmProv_eq_iff` / `minirust_*_decodeM`. -/
theorem ep2_b1_mr_non_vacuity_instances :
    decodeScalarLayoutBytesNoForge (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩) wP .strictUcg630Ub 8 =
      some (.ptr { allocId := 7, offsetBytes := 0x1000 } 8) ∧
    decodeScalarLayoutBytesNoForge (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩) wPlain .strictUcg630Ub 8 =
      some (.scalar ⟨0x1000, 8⟩) ∧
    decodeScalarLayoutBytesNoForge (.union (.pointer 0)) (encodePtrBytes 0x1000 4 9 9) .strictUcg630Ub 4 =
      some (.ptr { allocId := 9, offsetBytes := 0x1000 } 4) ∧
    decodeScalarLayoutBytesNoForge (.union (.pointer 0)) (encodePlainLittleEndianBytes 0x1000 4) .strictUcg630Ub 4 =
      some (.scalar ⟨0x1000, 4⟩) ∧
    (decodeScalarLayoutBytesNoForge (.initialized (.int 64 false) ⟨0, 0xFFFFFFFFFFFFFFFF⟩) wP .strictUcg630Ub 8 = none ∧
     decodeScalarLayoutBytesNoForge (.union (.int 64 false)) wP .strictUcg630Ub 8 = none) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 wP = thinDecode true 8 wP ∧
    decodePtrBytesNoForge true .str 8 (wP ++ wLen3) =
      (match thinDecode true 8 wP, sliceMetaDecode 8 wLen3 with
       | some dv, some mv => some (.aggregate 0 [dv, mv]) | _, _ => none) ∧
    decodePtrBytesNoForge true (.dynamic "T") 8 (wP ++ wVt) =
      (match thinDecode true 8 wP, thinDecode true 8 wVt with
       | some dv, some mv => some (.aggregate 0 [dv, mv]) | _, _ => none) ∧
    encodeUntypedValueToBytes 1 (.ptr ⟨7, 0x1000⟩ 8) = some wP ∧
    encodeValueToBytes 1 wLayouts wTyRawPtrU8 (.ptr ⟨7, 0x1000⟩ 8) = some wP ∧
    projBytes tbProv wPlain = Interp.encodePtrBytesM (M := Interp.TBM) none 0 (Interp.leBytes 0x1000 8) ∧
    (mrProvM Interp.TBM (projBytes tbProv wP)).isSome = true ∧
    thinDecode false 8 wPlain = some (.scalar ⟨0x1000, 8⟩) ∧
    thinDecode true 8 wPlain = none ∧
    thinDecode false 8 (wP.take 7 ++ [.uninit]) = none ∧
    (bmProv 7 7 = bmProv 7 9 ↔ (7 : Nat) = 7) ∧
    Interp.decodePtr (projBytes bmProv wP) = Interp.decodePtrM (M := Interp.BM) (projBytes bmProv wP) ∧
    Interp.encodePtr ⟨0x1000, some (bmProv 7 7)⟩ = Interp.encodePtrM (M := Interp.BM) ⟨0x1000, some (bmProv 7 7)⟩ ∧
    Interp.decodePtrProvenance 0 (Interp.firstProvenance (projBytes bmProv wP)) (projBytes bmProv wP) =
      Interp.decodePtrProvenanceM (M := Interp.BM) 0 (Interp.firstProvenance (projBytes bmProv wP)) (projBytes bmProv wP) ∧
    (∃ d, trData wP.reverse = some d ∧ thinDecode false 8 wP.reverse = some (.scalar ⟨Interp.leValue d, 8⟩) ∧
      thinDecode true 8 wP.reverse = none ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv wP.reverse) =
        .ok (some { addr := ((Interp.leValue d : Nat) : Int), provenance := none })) ∧
    (∃ d, trData (wP.take 1 ++ wP256.drop 1) = some d ∧
      thinDecode false 8 (wP.take 1 ++ wP256.drop 1) = some (.scalar ⟨Interp.leValue d, 8⟩) ∧
      thinDecode true 8 (wP.take 1 ++ wP256.drop 1) = none ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (wP.take 1 ++ wP256.drop 1)) =
        .ok (some { addr := ((Interp.leValue d : Nat) : Int), provenance := some (tbProv 7 7) })) ∧
    Interp.encodeWidePtrM (M := Interp.TBM) .ElementCount
      { thin_pointer := { addr := ((0x1000 : Nat) : Int), provenance := some (tbProv 7 7) },
        metadata := some (.ElementCount ((3 : Nat) : Int)) } =
      .ok (projBytes tbProv (wP ++ wLen3)) ∧
    Interp.encodeWidePtrM (M := Interp.TBM) (.VTablePointer ⟨⟨0⟩⟩)
      { thin_pointer := { addr := ((0x1000 : Nat) : Int), provenance := some (tbProv 7 7) },
        metadata := some (.VTablePointer { addr := ((0x80 : Nat) : Int), provenance := some (tbProv 42 42) }) } =
      .ok (projBytes tbProv (wP ++ wVt)) ∧
    (∃ dd, trData wP = some dd ∧
      decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (wP ++ wLen3) =
        some (.aggregate 0 [.ptr { allocId := 7, offsetBytes := Interp.leValue dd } 8,
          .scalar ⟨Interp.leValue [3, 0, 0, 0, 0, 0, 0, 0], 8⟩]) ∧
      decodePtrBytesNoForge true .str 8 (wP ++ wLen3) =
        some (.aggregate 0 [.ptr { allocId := 7, offsetBytes := Interp.leValue dd } 8,
          .scalar ⟨Interp.leValue [3, 0, 0, 0, 0, 0, 0, 0], 8⟩]) ∧
      Interp.decodeWidePtrM (M := Interp.TBM) .ElementCount (projBytes tbProv (wP ++ wLen3)) =
        .ok (some (.Ptr {
          thin_pointer := { addr := ((Interp.leValue dd : Nat) : Int), provenance := some (tbProv 7 7) },
          metadata := some (.ElementCount ((Interp.leValue [3, 0, 0, 0, 0, 0, 0, 0] : Nat) : Int)) }))) ∧
    (∃ dd md, trData wP = some dd ∧ trData wVt = some md ∧
      decodePtrBytesNoForge true (.dynamic "T") 8 (wP ++ wVt) =
        some (.aggregate 0 [.ptr { allocId := 7, offsetBytes := Interp.leValue dd } 8,
          .ptr { allocId := 42, offsetBytes := Interp.leValue md } 8]) ∧
      Interp.decodeWidePtrM (M := Interp.TBM) (.VTablePointer ⟨⟨0⟩⟩) (projBytes tbProv (wP ++ wVt)) =
        .ok (some (.Ptr {
          thin_pointer := { addr := ((Interp.leValue dd : Nat) : Int), provenance := some (tbProv 7 7) },
          metadata := some (.VTablePointer {
            addr := ((Interp.leValue md : Nat) : Int), provenance := some (tbProv 42 42) }) }))) ∧
    (∃ dd, trData wP = some dd ∧
      decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (wLen3 ++ wP) = none ∧
      Interp.decodeWidePtrM (M := Interp.TBM) .ElementCount (projBytes tbProv (wLen3 ++ wP)) =
        .ok (some (.Ptr {
          thin_pointer := { addr := ((Interp.leValue [3, 0, 0, 0, 0, 0, 0, 0] : Nat) : Int), provenance := none },
          metadata := some (.ElementCount ((Interp.leValue dd : Nat) : Int)) }))) ∧
    (decodeUntypedStorageBytes defaultCodecFuel wLayouts wTyBool [.init 2 none] = some (.scalar ⟨2, 1⟩) ∧
     ((decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyBool [.init 2 none]).isSome = true ↔
       ∃ b, Interp.Type.decodeM (M := Interp.TBM) .Bool (projBytes tbProv [.init 2 none]) = .ok (some (.Bool b))) ∧
     (validateValueForTy? wLayouts (some wTyBool) (.scalar ⟨(2 : UInt8).toNat, 1⟩) = true ↔
       ∃ b, Interp.Type.decodeM (M := Interp.TBM) .Bool (projBytes tbProv [.init 2 none]) = .ok (some (.Bool b)))) :=
  ⟨scalarLayoutPtr_coherent 0 ⟨0, 0xFFFFFFFFFFFFFFFF⟩ wP 0x1000 ⟨7, 7, 0, 0x1000, 8⟩ .strictUcg630Ub rfl rfl rfl rfl,
   scalarLayoutPtr_incoherent 0 ⟨0, 0xFFFFFFFFFFFFFFFF⟩ wPlain 0x1000 .strictUcg630Ub rfl rfl rfl,
   scalarLayoutPtr_union_coherent 0 4 (encodePtrBytes 0x1000 4 9 9) 0x1000 ⟨9, 9, 0, 0x1000, 4⟩ .strictUcg630Ub (by decide) rfl rfl rfl rfl,
   scalarLayoutPtr_union_incoherent 0 4 (encodePlainLittleEndianBytes 0x1000 4) 0x1000 .strictUcg630Ub (by decide) rfl rfl rfl,
   scalarLayoutNonPtr_strictUb_rejects_prov 64 false ⟨0, 0xFFFFFFFFFFFFFFFF⟩ 8 wP rfl,
   decodePtrBytesNoForge_thin true (.uint .u8) 8 wP rfl,
   decodePtrBytesNoForge_str true wP wLen3 (by decide) rfl,
   decodePtrBytesNoForge_dyn true "T" wP wVt (by decide) rfl,
   encodeUntyped_ptr 0 ⟨7, 0x1000⟩ 8 (by decide),
   encodeValueToBytes_thinPtr 0 wLayouts wTyRawPtrU8 ⟨7, 0x1000⟩ 8 rfl (by decide) (Or.inl ⟨.not, .uint .u8, rfl, rfl⟩),
   proj_plain_bytes (M := Interp.TBM) tbProv 8 0x1000 0,
   trusted_retains_implies_minirust_retains (M := Interp.TBM) tbProv wP rfl,
   thinDecode_raw_incoherent 8 wPlain 0x1000 (by decide) rfl rfl rfl,
   thinDecode_ref_incoherent 8 wPlain rfl,
   thinDecode_uninit false 8 (wP.take 7 ++ [.uninit]) rfl,
   bmProv_eq_iff 7 7 7 9,
   decodePtr_eq_M (projBytes bmProv wP),
   encodePtr_eq_M ⟨0x1000, some (bmProv 7 7)⟩,
   decodePtrProvenance_eq_M (projBytes bmProv wP) 0 (Interp.firstProvenance (projBytes bmProv wP)),
   (w1_transforms_decode_strips (M := Interp.TBM) tbProv 0x1000 7 7).1,
   offset_splice_decode_divergence (M := Interp.TBM) tbProv (wP.take 1 ++ wP256.drop 1)
     0x1000 0x1100 7 7 0 1 _ _ rfl
     (by intro k b hk; match k, hk with
       | 0, h => exact Or.inl h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h => exact Or.inr h
       | _ + 8, h => cases h)
     rfl rfl rfl rfl (by decide),
   encodeWidePtrM_slice_proj (M := Interp.TBM) tbProv 0x1000 3 7 7 (by decide) (by decide),
   encodeWidePtrM_dyn_proj (M := Interp.TBM) ⟨⟨0⟩⟩ tbProv 0x1000 0x80 7 7 42 42 (by decide) (by decide),
   coherent_wide_slice_decode_agreement (M := Interp.TBM) tbProv true (.uint .u8) wP wLen3
     ⟨7, 7, 0, 0x1000, 8⟩ [3, 0, 0, 0, 0, 0, 0, 0] rfl rfl rfl rfl rfl rfl,
   coherent_wide_dyn_decode_agreement (M := Interp.TBM) tbProv true "T" ⟨⟨0⟩⟩ wP wVt
     ⟨7, 7, 0, 0x1000, 8⟩ ⟨42, 42, 0, 0x80, 8⟩ rfl rfl rfl rfl rfl rfl,
   swapped_wide_slice_div (M := Interp.TBM) tbProv true (.uint .u8) wLen3 wP
     ⟨7, 7, 0, 0x1000, 8⟩ [3, 0, 0, 0, 0, 0, 0, 0] rfl rfl rfl ⟨3, rfl⟩ rfl,
   kani5205_bool_correspondence_M (M := Interp.TBM) tbProv wLayouts wTyBool rfl 2⟩


/-- **Universal `DIV-MR-CHAR` (`Kani#5205`, `char`).** For every 32-bit pattern `c`, `Trusted`'s
typed `char` validity is exactly `isValidCharCode c` (rejecting every surrogate and every value
above `0x10FFFF`), the `Trusted` untyped encoding of `c` projects to MiniRust's own little-endian
encoding of `c`, and MiniRust's closest type `Type::Int(u32)` accepts that encoding for every `c`.
MiniRust has no `char` type, so the typed rejection is `Trusted`-only. -/
theorem kani5205_char_divergence (c : Nat) (hc : c < 2 ^ 32) :
    validateValueForTy? wLayouts (some wTyChar) (.scalar ⟨c, 4⟩) = isValidCharCode c ∧
    projBytes bmProv (encodePlainLittleEndianBytes c 4) =
      (Interp.leBytes c 4).map (fun b => Gen.AbstractByte.Init b none) ∧
    Interp.Type.decode (.Int ⟨.Unsigned, ⟨4⟩⟩) (projBytes bmProv (encodePlainLittleEndianBytes c 4)) =
      .ok (some (.Int c)) := by
  have hp : projBytes bmProv (encodePlainLittleEndianBytes c 4) =
      (Interp.leBytes c 4).map (fun b => Gen.AbstractByte.Init b none) :=
    (proj_plain_bytes (M := Interp.BM) bmProv 4 c 0).trans (encodePtrBytesM_none _ 0)
  refine ⟨?_, hp, ?_⟩
  · show Bool.and (Nat.beq 4 4) (isValidCharCode c) = isValidCharCode c
    rfl
  · rw [hp]
    exact minirust_u32_accepts_all c hc

theorem kani5205_char_divergence_instance :
    (validateValueForTy? wLayouts (some wTyChar) (.scalar ⟨0xD800, 4⟩) = isValidCharCode 0xD800 ∧
      projBytes bmProv (encodePlainLittleEndianBytes 0xD800 4) =
        (Interp.leBytes 0xD800 4).map (fun b => Gen.AbstractByte.Init b none) ∧
      Interp.Type.decode (.Int ⟨.Unsigned, ⟨4⟩⟩) (projBytes bmProv (encodePlainLittleEndianBytes 0xD800 4)) =
        .ok (some (.Int 0xD800))) ∧
    isValidCharCode 0xD800 = false ∧ isValidCharCode 0x41 = true :=
  ⟨kani5205_char_divergence 0xD800 (by decide), rfl, rfl⟩

/-- Decoding LE bits of `encodePlainLittleEndianBytes c n` yields `c % 256 ^ n`. -/
theorem decodeLittleEndianBits_encodePlain :
    ∀ (n c : Nat), decodeLittleEndianBits (encodePlainLittleEndianBytes c n) = some (c % 256 ^ n)
  | 0, c => by
      show some 0 = some (c % 256 ^ 0)
      rw [Nat.pow_zero, Nat.mod_one]
  | n + 1, c => by
      show (match decodeLittleEndianBits (encodePlainLittleEndianBytes (c / 256) n) with
        | some hi => some (Nat.add (UInt8.ofNat c).toBitVec.toNat (Nat.mul 256 hi))
        | none => none) = some (c % 256 ^ (n + 1))
      rw [decodeLittleEndianBits_encodePlain n (c / 256)]
      show some ((UInt8.ofNat c).toNat + 256 * (c / 256 % 256 ^ n)) = some (c % 256 ^ (n + 1))
      rw [u8_ofNat_toNat, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]

/-- **Universal `Kani#5205` `char` correspondence across BOTH `BasicMemory` and `TreeBorrowsMemory`
via MiniRust's `Type::Enum` + `Discriminator::Branch` encoding (`minirustCharType`).**
For every 32-bit pattern `c < 2^32`, any `layouts`, any `tyChar` with `tyChar.kind = .char`, and
any `M ∈ {BasicMemory, TreeBorrowsMemory}`:
1. Untyped byte storage (`decodeUntypedStorageBytes`) succeeds for EVERY `c` (including all 2048
   surrogates `0xD800..=0xDFFF` and `> 0x10FFFF`, matching MiniRust `Type::Int(u32)` / `Type::Union`).
2. `Trusted.validateValueForTy?` and `Trusted.decodeTypedValueFromBytes` accept `c` **iff**
   MiniRust `Type.decodeM (M := M) minirustCharType` accepts the projected bytes! -/
theorem kani5205_char_correspondence_M {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M)
    (layouts : LayoutTable) (tyChar : Ty) (hty : tyChar.kind = .char)
    (c : Nat) (hc : c < 2 ^ 32) :
    let bs := encodePlainLittleEndianBytes c 4
    decodeUntypedStorageBytes defaultCodecFuel layouts tyChar bs = some (.scalar ⟨c, 4⟩) ∧
    ((decodeTypedValueFromBytes defaultCodecFuel layouts tyChar bs).isSome = true ↔
      ∃ v, Interp.Type.decodeM (M := M) minirustCharType (projBytes pv bs) = .ok (some v)) ∧
    (validateValueForTy? layouts (some tyChar) (.scalar ⟨c, 4⟩) = true ↔
      ∃ v, Interp.Type.decodeM (M := M) minirustCharType (projBytes pv bs) = .ok (some v)) := by
  intro bs
  obtain ⟨kind, lidx⟩ := tyChar
  dsimp only at hty
  subst hty
  have hp : projBytes pv bs =
      (Interp.leBytes c 4).map (fun b => Gen.AbstractByte.Init b none) :=
    (proj_plain_bytes (M := M) pv 4 c 0).trans (encodePtrBytesM_none_eq_map _ 0)
  have hbits : decodeLittleEndianBits bs = some c := by
    have h := decodeLittleEndianBits_encodePlain 4 c
    rw [Nat.mod_eq_of_lt (by omega : c < 256 ^ 4)] at h
    exact h
  have hlen : length bs = 4 := rfl
  have hnoprov : abstractBytesHaveProv bs = false := rfl
  have hunt : decodeUntypedStorageBytes defaultCodecFuel layouts { kind := .char, layoutIdx := lidx } bs =
      some (.scalar ⟨c, 4⟩) := by
    show (match Nat.beq (length bs) 4, policyRejectsProv .strictUcg630Ub bs with
      | true, false => match decodeLittleEndianBits bs with
        | some bits => some (Value.scalar ⟨bits, 4⟩)
        | none => none
      | _, _ => none) = some (.scalar ⟨c, 4⟩)
    have hpol : policyRejectsProv .strictUcg630Ub bs = false := by
      unfold policyRejectsProv; exact hnoprov
    rw [hlen, hpol, hbits]
  have hsc : decodeScalarBytes bs false = some ({ bits := c, sizeBytes := 4 }, none) := by
    unfold decodeScalarBytes decodeLittleEndianBytes
    rw [hlen, hbits]
  have hvalid_iff : isValidCharCode c = true ↔ (c < 0xD800 ∨ (0xE000 ≤ c ∧ c ≤ 0x10FFFF)) := by
    unfold isValidCharCode
    constructor
    · intro h
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
      rcases h with h1 | ⟨h2, h3⟩
      · left
        cases hc1 : Nat.ble 55296 c with
        | true => rw [hc1] at h1; cases h1
        | false =>
          by_cases hlt : c < 55296
          · exact hlt
          · have : 55296 ≤ c := by omega
            have := Nat.ble_eq.mpr this
            rw [this] at hc1; cases hc1
      · right; rw [Nat.ble_eq] at h2 h3; exact ⟨h2, h3⟩
    · intro h
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
      rcases h with h1 | ⟨h2, h3⟩
      · left
        cases hc1 : Nat.ble 55296 c with
        | false => rfl
        | true => have := Nat.ble_eq.mp hc1; omega
      · right; exact ⟨Nat.ble_eq.mpr h2, Nat.ble_eq.mpr h3⟩
  have hdec : decodeTypedValueFromBytes defaultCodecFuel layouts { kind := .char, layoutIdx := lidx } bs =
      if isValidCharCode c then some (.scalar ⟨c, 4⟩) else none := by
    show (match abstractBytesHaveProv bs with
      | true => none
      | false =>
        match Nat.beq (length bs) 4 with
        | false => none
        | true =>
          match decodeScalarBytes bs false with
          | some (sv, _) =>
            match isValidCharCode sv.bits with
            | true => some (Value.scalar sv)
            | false => none
          | none => none) = _
    rw [hnoprov, hlen, hsc]
    dsimp only
    cases isValidCharCode c <;> rfl
  have hval : validateValueForTy? layouts (some { kind := .char, layoutIdx := lidx }) (.scalar ⟨c, 4⟩) =
      isValidCharCode c := by
    show Bool.and (Nat.beq 4 4) (isValidCharCode c) = isValidCharCode c
    rfl
  rw [hp, minirust_char_decodeM_iff (M := M) c hc, hdec, hval]
  refine ⟨hunt, ?_, hvalid_iff⟩
  cases h : isValidCharCode c with
  | true => simp [hvalid_iff.mp h]
  | false =>
    constructor
    · intro hf; cases hf
    · intro hok; exact absurd (hvalid_iff.mpr hok) (by rw [h]; decide)

/-- Non-vacuous boundary instantiations of `kani5205_char_correspondence_M` across `BM` and `TBM`
(valid ASCII `0x41`, BMP edge `0xD7FF`, surrogates `0xD800`/`0xDFFF`, post-surrogate `0xE000`,
max Unicode `0x10FFFF`, out-of-range `0x110000`, plus `.Uninit`). -/
theorem w_kani5205_char_enum_instance :
    Interp.Type.decodeM (M := Interp.BM) minirustCharType
        (projBytes bmProv (encodePlainLittleEndianBytes 0x41 4)) = .ok (some (.Variant 0 (.Int 0x41))) ∧
    Interp.Type.decodeM (M := Interp.TBM) minirustCharType
        (projBytes tbProv (encodePlainLittleEndianBytes 0xD7FF 4)) = .ok (some (.Variant 0 (.Int 0xD7FF))) ∧
    Interp.Type.decodeM (M := Interp.TBM) minirustCharType
        (projBytes tbProv (encodePlainLittleEndianBytes 0xD800 4)) = .ok none ∧
    Interp.Type.decodeM (M := Interp.BM) minirustCharType
        (projBytes bmProv (encodePlainLittleEndianBytes 0xDFFF 4)) = .ok none ∧
    Interp.Type.decodeM (M := Interp.TBM) minirustCharType
        (projBytes tbProv (encodePlainLittleEndianBytes 0xE000 4)) = .ok (some (.Variant 1 (.Int 0xE000))) ∧
    Interp.Type.decodeM (M := Interp.TBM) minirustCharType
        (projBytes tbProv (encodePlainLittleEndianBytes 0x10FFFF 4)) = .ok (some (.Variant 1 (.Int 0x10FFFF))) ∧
    Interp.Type.decodeM (M := Interp.TBM) minirustCharType
        (projBytes tbProv (encodePlainLittleEndianBytes 0x110000 4)) = .ok none ∧
    Interp.Type.decodeM (M := Interp.TBM) minirustCharType [.Uninit, .Init 0 none, .Init 0 none, .Init 0 none] = .ok none ∧
    (decodeUntypedStorageBytes defaultCodecFuel wLayouts wTyChar (encodePlainLittleEndianBytes 0xD800 4) =
        some (.scalar ⟨0xD800, 4⟩) ∧
      ((decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyChar (encodePlainLittleEndianBytes 0xD800 4)).isSome = true ↔
        ∃ v, Interp.Type.decodeM (M := Interp.TBM) minirustCharType
          (projBytes tbProv (encodePlainLittleEndianBytes 0xD800 4)) = .ok (some v)) ∧
      (validateValueForTy? wLayouts (some wTyChar) (.scalar ⟨0xD800, 4⟩) = true ↔
        ∃ v, Interp.Type.decodeM (M := Interp.TBM) minirustCharType
          (projBytes tbProv (encodePlainLittleEndianBytes 0xD800 4)) = .ok (some v))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, minirust_char_uninit_decodeM _ _ _,
    kani5205_char_correspondence_M (M := Interp.TBM) tbProv wLayouts wTyChar rfl 0xD800 (by decide)⟩
  · rw [(proj_plain_bytes (M := Interp.BM) bmProv 4 0x41 0).trans (encodePtrBytesM_none_eq_map _ 0)]
    exact minirust_char_decodeM_eq (M := Interp.BM) 0x41 (by decide)
  · rw [(proj_plain_bytes (M := Interp.TBM) tbProv 4 0xD7FF 0).trans (encodePtrBytesM_none_eq_map _ 0)]
    exact minirust_char_decodeM_eq (M := Interp.TBM) 0xD7FF (by decide)
  · rw [(proj_plain_bytes (M := Interp.TBM) tbProv 4 0xD800 0).trans (encodePtrBytesM_none_eq_map _ 0)]
    exact minirust_char_decodeM_eq (M := Interp.TBM) 0xD800 (by decide)
  · rw [(proj_plain_bytes (M := Interp.BM) bmProv 4 0xDFFF 0).trans (encodePtrBytesM_none_eq_map _ 0)]
    exact minirust_char_decodeM_eq (M := Interp.BM) 0xDFFF (by decide)
  · rw [(proj_plain_bytes (M := Interp.TBM) tbProv 4 0xE000 0).trans (encodePtrBytesM_none_eq_map _ 0)]
    exact minirust_char_decodeM_eq (M := Interp.TBM) 0xE000 (by decide)
  · rw [(proj_plain_bytes (M := Interp.TBM) tbProv 4 0x10FFFF 0).trans (encodePtrBytesM_none_eq_map _ 0)]
    exact minirust_char_decodeM_eq (M := Interp.TBM) 0x10FFFF (by decide)
  · rw [(proj_plain_bytes (M := Interp.TBM) tbProv 4 0x110000 0).trans (encodePtrBytesM_none_eq_map _ 0)]
    exact minirust_char_decodeM_eq (M := Interp.TBM) 0x110000 (by decide)

/-- Little-endian optional byte list for a `CapturedAllocation` (no uninit bytes). -/
def leOptBytes (u : Nat) : Nat → List (Option UInt8)
  | 0 => []
  | n + 1 => some (UInt8.ofNat u) :: leOptBytes (u / 256) n

/-- **Universal `body.globals` relocation correspondence (`Trusted` ↔ `MiniRustSpec.Interp`,
64-bit, BOTH `BasicMemory` and `TreeBorrowsMemory`).**
For any global `CapturedAllocation` holding an 8-byte pointer relocation `(0, targetPtr)` with LE
bytes of any `addr < 2^64`, `globalAllocSliceToAbstractBytes` equals `encodePtrBytes`, projects to
MiniRust `encodePtrM`, decodes identically in `Trusted.evalGlobalDerefRead` (raw `*const u8` &
`&u8`) and `MiniRustSpec.Interp.decodePtrM`, and faults with `.ub` on a typed `u64` dereference
read under `.strictUcg630Ub` (`W5`). -/
theorem globalAlloc_reloc_correspondence_M {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M)
    (gId : Nat) (al : Align) (mutbl : Mutability) (targetPtr : ProvenancePtr)
    (addr : Nat) (haddr : addr < 2 ^ 64) :
    let alloc : CapturedAllocation :=
      { allocId := gId, bytes := leOptBytes addr 8, relocations := [(0, targetPtr)],
        align := al, mutability := mutbl }
    let bs := encodePtrBytes addr 8 targetPtr.allocId targetPtr.tag
    globalAllocSliceToAbstractBytes alloc 0 8 8 = some bs ∧
    Interp.encodePtrM (M := M) ⟨(addr : Int), some (pv targetPtr.allocId targetPtr.tag)⟩ =
      .ok (projBytes pv bs) ∧
    Interp.decodePtrM (M := M) (projBytes pv bs) =
      .ok (some ⟨(addr : Int), some (pv targetPtr.allocId targetPtr.tag)⟩) ∧
    evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some wTyRawPtrU8) =
      .ok (.ptr { allocId := targetPtr.allocId, offsetBytes := addr } 8) [] ∧
    evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some { kind := .ref .not (.uint .u8), layoutIdx := 0 }) =
      .ok (.ptr { allocId := targetPtr.allocId, offsetBytes := addr } 8) [] ∧
    evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some { kind := .uint .u64, layoutIdx := 0 }) = .ub := by
  intro alloc bs
  have hbits8 :
      Nat.add (UInt8.ofNat addr).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256 / 256 / 256)).toBitVec.toNat
        (Nat.mul 256 0))))))))))))))) = addr := by
    have h := decodeLittleEndianBits_encodePlain 8 addr
    rw [Nat.mod_eq_of_lt (by omega : addr < 256 ^ 8)] at h
    injection h with h
  have horig : readGlobalRelocOrigOffset (leOptBytes addr 8) 0 8 targetPtr = normPtrByteOffset 8 addr := by
    unfold readGlobalRelocOrigOffset
    show (match some (Nat.add (UInt8.ofNat addr).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256 / 256)).toBitVec.toNat (Nat.mul 256
      (Nat.add (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256 / 256 / 256)).toBitVec.toNat
        (Nat.mul 256 0)))))))))))))))) with
      | some bits => normPtrByteOffset 8 bits
      | none => normPtrByteOffset 8 targetPtr.offsetBytes) = normPtrByteOffset 8 addr
    rw [hbits8]
  have hslice : globalAllocSliceToAbstractBytes alloc 0 8 8 = some bs := by
    unfold globalAllocSliceToAbstractBytes
    dsimp only [alloc, bs, encodePtrBytes, encodePtrBytesAux]
    simp only [globalAllocBytesAux, leOptBytes, lookupRelocEntry, get?, Nat.ble, Nat.blt,
      Nat.add, Nat.sub, Bool.and, Bool.not]
    have horig' : readGlobalRelocOrigOffset
        [some (UInt8.ofNat addr), some (UInt8.ofNat (addr / 256)),
         some (UInt8.ofNat (addr / 256 / 256)), some (UInt8.ofNat (addr / 256 / 256 / 256)),
         some (UInt8.ofNat (addr / 256 / 256 / 256 / 256)),
         some (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256)),
         some (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256 / 256)),
         some (UInt8.ofNat (addr / 256 / 256 / 256 / 256 / 256 / 256 / 256))] 0 8 targetPtr =
        normPtrByteOffset 8 addr := horig
    rw [horig']; rfl
  have henc := encodePtrM_proj (M := M) pv addr targetPtr.allocId targetPtr.tag haddr
  have hdecM := decodePtrM_proj_encodePtrBytes (M := M) pv addr targetPtr.allocId targetPtr.tag haddr
  have hthin : ∀ isRef, decodePtrBytesNoForge isRef (.uint .u8) 8 bs =
      some (.ptr { allocId := targetPtr.allocId, offsetBytes := addr } 8) := by
    intro isRef
    have h := (decodePtrBytesNoForge_thin isRef (.uint .u8) 8 bs rfl).trans
      (thinDecode_encodePtrBytes isRef addr 8 targetPtr.allocId targetPtr.tag (by decide))
    rw [Nat.mod_eq_of_lt (by omega : addr < 256 ^ 8)] at h
    exact h
  have hraw : evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some wTyRawPtrU8) =
      .ok (.ptr { allocId := targetPtr.allocId, offsetBytes := addr } 8) [] := by
    unfold evalGlobalDerefRead
    simp only [wLayouts, wTyRawPtrU8, layoutPointerBytes, intCastTargetBytes, hslice]
    change (match decodePtrBytesNoForge false (.uint .u8) 8 bs with
      | some decodedVal =>
        match readProjectedValue [] decodedVal [] with
        | .ok fieldVal => PlaceReadResult.ok fieldVal []
        | .ub => .ub | .unsupported => .unsupported
      | none => .ub) = _
    rw [hthin false]; rfl
  have href : evalGlobalDerefRead [] alloc 0 8 [] wLayouts
      (some { kind := .ref .not (.uint .u8), layoutIdx := 0 }) =
      .ok (.ptr { allocId := targetPtr.allocId, offsetBytes := addr } 8) [] := by
    unfold evalGlobalDerefRead
    simp only [wLayouts, layoutPointerBytes, intCastTargetBytes, hslice]
    change (match decodePtrBytesNoForge true (.uint .u8) 8 bs with
      | some decodedVal =>
        match readProjectedValue [] decodedVal [] with
        | .ok fieldVal => PlaceReadResult.ok fieldVal []
        | .ub => .ub | .unsupported => .unsupported
      | none => .ub) = _
    rw [hthin true]; rfl
  have hu64 : evalGlobalDerefRead [] alloc 0 8 [] wLayouts
      (some { kind := .uint .u64, layoutIdx := 0 }) = .ub := rfl
  exact ⟨hslice, henc, hdecM, hraw, href, hu64⟩

def wPtrL : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false, fieldLayouts := [] }
def wArr8U8L : TypeLayout :=
  { size := ⟨8⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .array ⟨1⟩ 8, variants := .single 0, isUninhabited := false, fieldLayouts := [1] }
def wCopyLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [wUnitL, wU8L, wBoolL, wCharL, wU32L, wPtrL, wArr8U8L] }
def wTyRawPtrC : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 5 }
def wTyRefC : Ty := { kind := .ref .not (.uint .u8), layoutIdx := 5 }
def wTyArr8U8C : Ty := { kind := .array (.uint .u8) 8, layoutIdx := 6 }
def wCopyMem : Memory :=
  { emptyMemory with
    borrows := [
      { tag := 10, targetLocal := 0, targetProjection := [], perm := .frozen, rangeOffset := 0, rangeLen := 8 },
      { tag := 11, targetLocal := 1, targetProjection := [], perm := .active, rangeOffset := 0, rangeLen := 8 }
    ] }
def wCopyStep (srcTy dstTy : Ty) (srcSlot dstSlot : LocalSlot) (sOff dOff n : Nat) :
    Option LocalSlot :=
  let decls : List LocalDecl := [
    { mutability := .not, ty := srcTy, debugName := none },
    { mutability := .mut, ty := dstTy, debugName := none }
  ]
  let l := [srcSlot, dstSlot]
  match evalCopyMemory { frame := { blockIdx := 0, stmtIdx := 0, locals := l }, memory := wCopyMem }
      l decls wCopyLayouts ⟨10, sOff⟩ ⟨11, dOff⟩ n with
  | .ok (_ :: dst' :: _, _) => some dst'
  | _ => none
def wCopyRead (srcTy dstTy : Ty) (srcSlot dstSlot : LocalSlot) (sOff dOff n : Nat) :
    Option (Option Value) :=
  let decls : List LocalDecl := [
    { mutability := .not, ty := srcTy, debugName := none },
    { mutability := .mut, ty := dstTy, debugName := none }
  ]
  let l := [srcSlot, dstSlot]
  match evalCopyMemory { frame := { blockIdx := 0, stmtIdx := 0, locals := l }, memory := wCopyMem }
      l decls wCopyLayouts ⟨10, sOff⟩ ⟨11, dOff⟩ n with
  | .ok (l', _) =>
    match evalOperand l' (.copy ⟨1, []⟩) [] [] wCopyLayouts [] decls with
    | .ok v _ => some (some v)
    | .ub => some none
    | .unsupported => none
  | _ => none

/-- **End-to-end `body.globals` misaligned relocation & `evalCopyMemory` correspondence witness
(`Trusted` ↔ `MiniRustSpec.Interp`).**
1. Misaligned `[p, p]` global relocation read at offset `4`: BOTH `Trusted.evalGlobalDerefRead`
   (raw -> `.scalar`, ref -> `.ub`) AND `MiniRust` `decodePtrM` strip provenance.
2. End-to-end `Trusted.evalCopyMemory`:
   - intact 8B copy retains `.ptr ⟨7, 0x1000⟩ 8` in `Trusted` and `some (tbProv 7 7)` in `MiniRust`;
   - 4+4 swapped halves strip provenance in BOTH `Trusted` and `MiniRust`;
   - 1+7 `p` / `p+256` splice via two `evalCopyMemory` calls strips in `Trusted` (raw -> `.scalar
     ⟨0x1100, 8⟩`, ref -> `.ub`) while `MiniRust` retains `some (tbProv 7 7)` (`DIV-MR-OFFSET-SPLICE`). -/
theorem w_mr_global_reloc_and_copyMemory :
    let p : ProvenancePtr := { allocId := 7, offsetBytes := 0x1000 }
    let p256 : ProvenancePtr := { allocId := 7, offsetBytes := 0x1100 }
    let adjAlloc : CapturedAllocation :=
      { allocId := 50, bytes := leOptBytes 0x1000 8 ++ leOptBytes 0x1000 8,
        relocations := [(0, p), (8, p)], align := ⟨8⟩, mutability := .not }
    (∃ misBytes, globalAllocSliceToAbstractBytes adjAlloc 4 8 8 = some misBytes ∧
      evalGlobalDerefRead [] adjAlloc 4 8 [] wLayouts (some wTyRawPtrU8) =
        .ok (.scalar ⟨0x100000000000, 8⟩) [] ∧
      evalGlobalDerefRead [] adjAlloc 4 8 [] wLayouts (some { kind := .ref .not (.uint .u8), layoutIdx := 0 }) = .ub ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv misBytes) = .ok (some ⟨0x100000000000, none⟩)) ∧
    (∃ vIntact bsIntact,
      wCopyRead wTyRawPtrC wTyRefC (.init (.ptr p 8)) .uninit 0 0 8 = some (some (.ptr ⟨7, 0x1000⟩ 8)) ∧
      wCopyStep wTyRawPtrC wTyArr8U8C (.init (.ptr p 8)) .uninit 0 0 8 = some (.init vIntact) ∧
      encodeUntypedValueToBytes defaultCodecFuel vIntact = some bsIntact ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv bsIntact) = .ok (some ⟨0x1000, some (tbProv 7 7)⟩)) ∧
    (∃ s1 vSwap bsSwap,
      wCopyStep wTyRawPtrC wTyArr8U8C (.init (.ptr p 8)) .uninit 0 4 4 = some s1 ∧
      wCopyStep wTyRawPtrC wTyArr8U8C (.init (.ptr p 8)) s1 4 0 4 = some (.init vSwap) ∧
      wCopyRead wTyArr8U8C wTyRawPtrC (.init vSwap) .uninit 0 0 8 = some (some (.scalar ⟨0x100000000000, 8⟩)) ∧
      wCopyRead wTyArr8U8C wTyRefC (.init vSwap) .uninit 0 0 8 = some none ∧
      encodeUntypedValueToBytes defaultCodecFuel vSwap = some bsSwap ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv bsSwap) = .ok (some ⟨0x100000000000, none⟩)) ∧
    (∃ s1 vSplice bsSplice,
      wCopyStep wTyRawPtrC wTyArr8U8C (.init (.ptr p 8)) .uninit 0 0 1 = some s1 ∧
      wCopyStep wTyRawPtrC wTyArr8U8C (.init (.ptr p256 8)) s1 1 1 7 = some (.init vSplice) ∧
      wCopyRead wTyArr8U8C wTyRawPtrC (.init vSplice) .uninit 0 0 8 = some (some (.scalar ⟨0x1100, 8⟩)) ∧
      wCopyRead wTyArr8U8C wTyRefC (.init vSplice) .uninit 0 0 8 = some none ∧
      encodeUntypedValueToBytes defaultCodecFuel vSplice = some bsSplice ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv bsSplice) = .ok (some ⟨0x1100, some (tbProv 7 7)⟩)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨_, rfl, rfl, rfl, rfl⟩
  · refine ⟨_, _, rfl, rfl, rfl, rfl⟩
  · refine ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Non-vacuous instantiations of `globalAlloc_reloc_correspondence_M` across both `BM` and `TBM`. -/
theorem ep2_b2_mr_non_vacuity_instances :
    let p : ProvenancePtr := { allocId := 7, offsetBytes := 0x1000 }
    let alloc : CapturedAllocation :=
      { allocId := 50, bytes := leOptBytes 0x1000 8, relocations := [(0, p)],
        align := ⟨8⟩, mutability := .not }
    (globalAllocSliceToAbstractBytes alloc 0 8 8 = some (encodePtrBytes 0x1000 8 7 7) ∧
      Interp.encodePtrM (M := Interp.TBM) ⟨0x1000, some (tbProv 7 7)⟩ =
        .ok (projBytes tbProv (encodePtrBytes 0x1000 8 7 7)) ∧
      Interp.decodePtrM (M := Interp.TBM) (projBytes tbProv (encodePtrBytes 0x1000 8 7 7)) =
        .ok (some ⟨0x1000, some (tbProv 7 7)⟩) ∧
      evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some wTyRawPtrU8) = .ok (.ptr ⟨7, 0x1000⟩ 8) [] ∧
      evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some { kind := .ref .not (.uint .u8), layoutIdx := 0 }) =
        .ok (.ptr ⟨7, 0x1000⟩ 8) [] ∧
      evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some { kind := .uint .u64, layoutIdx := 0 }) = .ub) ∧
    (globalAllocSliceToAbstractBytes alloc 0 8 8 = some (encodePtrBytes 0x1000 8 7 7) ∧
      Interp.encodePtrM (M := Interp.BM) ⟨0x1000, some (bmProv 7 7)⟩ =
        .ok (projBytes bmProv (encodePtrBytes 0x1000 8 7 7)) ∧
      Interp.decodePtrM (M := Interp.BM) (projBytes bmProv (encodePtrBytes 0x1000 8 7 7)) =
        .ok (some ⟨0x1000, some (bmProv 7 7)⟩) ∧
      evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some wTyRawPtrU8) = .ok (.ptr ⟨7, 0x1000⟩ 8) [] ∧
      evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some { kind := .ref .not (.uint .u8), layoutIdx := 0 }) =
        .ok (.ptr ⟨7, 0x1000⟩ 8) [] ∧
      evalGlobalDerefRead [] alloc 0 8 [] wLayouts (some { kind := .uint .u64, layoutIdx := 0 }) = .ub) :=
  ⟨globalAlloc_reloc_correspondence_M (M := Interp.TBM) tbProv 50 ⟨8⟩ .not { allocId := 7, offsetBytes := 0x1000 } 0x1000 (by decide),
   globalAlloc_reloc_correspondence_M (M := Interp.BM) bmProv 50 ⟨8⟩ .not { allocId := 7, offsetBytes := 0x1000 } 0x1000 (by decide)⟩

end Witnesses

end V08

/-! ## Lockstep parity `V2026_06_01 ↔ V2026_08_01`

The two dialects have distinct `AbstractByte` / `PtrByteFrag` / `Value` types.
`byte68` is the identity translation between them; every codec operation that
the correspondence theorems use commutes with it, so the `V06` and `V08`
correspondence statements are the same statement. -/

section Parity

/-- The identity translation of fragments from `V2026_06_01` to `V2026_08_01`. -/
def frag68 (f : Trusted.Rustc.V2026_06_01.MirSemantics.PtrByteFrag) :
    Trusted.Rustc.V2026_08_01.MirSemantics.PtrByteFrag :=
  ⟨f.allocId, f.tag, f.byteIdx, f.origOffset, f.ptrBytes⟩

/-- The identity translation of abstract bytes from `V2026_06_01` to `V2026_08_01`. -/
def byte68 : Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte →
    Trusted.Rustc.V2026_08_01.MirSemantics.AbstractByte
  | .uninit => .uninit
  | .init b none => .init b none
  | .init b (some f) => .init b (some (frag68 f))

theorem byte68_init (b : UInt8)
    (pr : Option Trusted.Rustc.V2026_06_01.MirSemantics.PtrByteFrag) :
    byte68 (.init b pr) = .init b (pr.map frag68) := by
  cases pr <;> rfl

/-- The version-independent view of a thin-pointer decode outcome: the bits, the
width, and the allocation of a `Value.ptr` (`none` for an integer). -/
def thinView06 : Option Trusted.Rustc.V2026_06_01.MirSemantics.Value → Option (Nat × Nat × Option Nat)
  | some (.ptr p sz) => some (p.offsetBytes, sz, some p.allocId)
  | some (.scalar sv) => some (sv.bits, sv.sizeBytes, none)
  | _ => none

/-- The version-independent view of a thin-pointer decode outcome (`V2026_08_01`). -/
def thinView08 : Option Trusted.Rustc.V2026_08_01.MirSemantics.Value → Option (Nat × Nat × Option Nat)
  | some (.ptr p sz) => some (p.offsetBytes, sz, some p.allocId)
  | some (.scalar sv) => some (sv.bits, sv.sizeBytes, none)
  | _ => none

theorem proj_parity {P : Type} (pv : Nat → Nat → P) :
    ∀ bs : List Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte,
      V08.projBytes pv (bs.map byte68) = V06.projBytes pv bs
  | [] => rfl
  | .uninit :: rest => congrArg (List.cons _) (proj_parity pv rest)
  | .init _ none :: rest => congrArg (List.cons _) (proj_parity pv rest)
  | .init _ (some _) :: rest => congrArg (List.cons _) (proj_parity pv rest)

theorem coherentAux_parity (a t o pb : Nat) :
    ∀ (bs : List Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte) (idx : Nat),
      Trusted.Rustc.V2026_08_01.MirSemantics.abstractBytesCoherentPtrProvAux a t o pb idx
          (bs.map byte68) =
        Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProvAux a t o pb idx bs
  | [], _ => rfl
  | .uninit :: _, _ => rfl
  | .init _ none :: _, _ => rfl
  | .init _ (some _) :: rest, idx =>
      congrArg (Bool.and _) (coherentAux_parity a t o pb rest (idx + 1))

/-- **Coherence parity.** `abstractBytesCoherentPtrProv?` commutes with the translation. -/
theorem coherent_parity (bs : List Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte) :
    Trusted.Rustc.V2026_08_01.MirSemantics.abstractBytesCoherentPtrProv? (bs.map byte68) =
      (Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProv? bs).map frag68 := by
  cases bs with
  | nil => rfl
  | cons b rest =>
      cases b with
      | uninit => rfl
      | init v pr =>
          cases pr with
          | none => rfl
          | some f =>
              show (match Bool.and (Nat.blt 0 f.ptrBytes) (Bool.and (Nat.beq f.byteIdx 0)
                    (Trusted.Rustc.V2026_08_01.MirSemantics.abstractBytesCoherentPtrProvAux
                      f.allocId f.tag f.origOffset f.ptrBytes 1 (rest.map byte68))) with
                | true => some (frag68 f)
                | false => none) =
                (match Bool.and (Nat.blt 0 f.ptrBytes) (Bool.and (Nat.beq f.byteIdx 0)
                    (Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProvAux
                      f.allocId f.tag f.origOffset f.ptrBytes 1 rest)) with
                | true => some f
                | false => none).map frag68
              rw [coherentAux_parity]
              cases Bool.and (Nat.blt 0 f.ptrBytes) (Bool.and (Nat.beq f.byteIdx 0)
                (Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProvAux
                  f.allocId f.tag f.origOffset f.ptrBytes 1 rest)) <;> rfl

theorem bits_parity :
    ∀ bs : List Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte,
      Trusted.Rustc.V2026_08_01.MirSemantics.decodeLittleEndianBits (bs.map byte68) =
        Trusted.Rustc.V2026_06_01.MirSemantics.decodeLittleEndianBits bs
  | [] => rfl
  | .uninit :: _ => rfl
  | .init b pr :: rest => by
      show Trusted.Rustc.V2026_08_01.MirSemantics.decodeLittleEndianBits
          (byte68 (.init b pr) :: rest.map byte68) = _
      rw [byte68_init]
      show (match Trusted.Rustc.V2026_08_01.MirSemantics.decodeLittleEndianBits (rest.map byte68) with
        | some highBits => some (Nat.add b.toBitVec.toNat (Nat.mul 256 highBits))
        | none => none) =
        (match Trusted.Rustc.V2026_06_01.MirSemantics.decodeLittleEndianBits rest with
        | some highBits => some (Nat.add b.toBitVec.toNat (Nat.mul 256 highBits))
        | none => none)
      rw [bits_parity rest]

theorem length_parity (bs : List Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte) :
    Trusted.Sequence.length (bs.map byte68) = Trusted.Sequence.length bs :=
  List.length_map _

theorem scalarModulus_parity :
    ∀ n : Nat, Trusted.Rustc.V2026_08_01.MirSemantics.scalarModulus n =
      Trusted.Rustc.V2026_06_01.MirSemantics.scalarModulus n
  | 0 => rfl
  | n + 1 => congrArg (Nat.mul 256) (scalarModulus_parity n)

theorem encodeAux_parity (a t o pb : Nat) :
    ∀ (n bits idx : Nat),
      Trusted.Rustc.V2026_08_01.MirSemantics.encodePtrBytesAux a t o pb bits idx n =
        (Trusted.Rustc.V2026_06_01.MirSemantics.encodePtrBytesAux a t o pb bits idx n).map byte68
  | 0, _, _ => rfl
  | n + 1, bits, idx =>
      congrArg (List.cons _) (encodeAux_parity a t o pb n (Nat.div bits 256) (Nat.add idx 1))

/-- **Encoding parity.** Both dialects encode a pointer to the same byte image. -/
theorem encode_parity (bits pb a t : Nat) :
    Trusted.Rustc.V2026_08_01.MirSemantics.encodePtrBytes bits pb a t =
      (Trusted.Rustc.V2026_06_01.MirSemantics.encodePtrBytes bits pb a t).map byte68 := by
  show Trusted.Rustc.V2026_08_01.MirSemantics.encodePtrBytesAux a t
      (Nat.mod bits (Trusted.Rustc.V2026_08_01.MirSemantics.scalarModulus pb)) pb bits 0 pb = _
  rw [scalarModulus_parity]
  exact encodeAux_parity a t _ pb pb bits 0

/-- **Decode parity.** The thin-pointer decoders of both dialects produce the same outcome. -/
theorem thinDecode_parity (isRef : Bool) (pb : Nat)
    (bs : List Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte) :
    thinView08 (V08.thinDecode isRef pb (bs.map byte68)) =
      thinView06 (V06.thinDecode isRef pb bs) := by
  unfold V08.thinDecode V06.thinDecode
  rw [bits_parity, coherent_parity, length_parity]
  cases Nat.blt 0 pb <;> cases Nat.beq (Trusted.Sequence.length bs) pb <;>
    cases Trusted.Rustc.V2026_06_01.MirSemantics.decodeLittleEndianBits bs <;> try rfl
  cases Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProv? bs with
  | none => cases isRef <;> rfl
  | some f =>
      simp only [Option.map, frag68]
      cases Nat.beq f.ptrBytes pb <;> cases isRef <;> rfl

/-- **`V2026_06_01 ↔ V2026_08_01` lockstep parity of the correspondence.** On
translated streams the two dialects have the same MiniRust projection, the same
coherence verdict, the same thin-pointer decode outcome, and therefore the same
MiniRust provenance verdict: every `V06` correspondence theorem and its `V08`
twin relate the same pair of behaviours. -/
theorem lockstep_parity {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    (pv : Nat → Nat → Gen.Memory.Provenance M) (isRef : Bool) (pb : Nat)
    (bs : List Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte) :
    V08.projBytes pv (bs.map byte68) = V06.projBytes pv bs ∧
    (Trusted.Rustc.V2026_08_01.MirSemantics.abstractBytesCoherentPtrProv? (bs.map byte68)).isSome =
      (Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProv? bs).isSome ∧
    thinView08 (V08.thinDecode isRef pb (bs.map byte68)) =
      thinView06 (V06.thinDecode isRef pb bs) ∧
    mrProvM M (V08.projBytes pv (bs.map byte68)) = mrProvM M (V06.projBytes pv bs) := by
  refine ⟨proj_parity pv bs, ?_, thinDecode_parity isRef pb bs, ?_⟩
  · rw [coherent_parity]
    cases Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProv? bs <;> rfl
  · rw [proj_parity]

/-- **Parity witnesses.** The fixtures of the two dialects are translations of
each other, and the `p` / `p + 256` splice is stripped by both dialects while
MiniRust retains its provenance on both projections. -/
theorem w_lockstep_parity :
    V06.wP.map byte68 = V08.wP ∧
    (V06.wP.take 1 ++ V06.wP256.drop 1).map byte68 = V08.wP.take 1 ++ V08.wP256.drop 1 ∧
    thinView06 (V06.thinDecode false 8 (V06.wP.take 1 ++ V06.wP256.drop 1)) =
      some (0x1100, 8, none) ∧
    thinView08 (V08.thinDecode false 8 (V08.wP.take 1 ++ V08.wP256.drop 1)) =
      some (0x1100, 8, none) ∧
    thinView06 (V06.thinDecode true 8 V06.wP) = some (0x1000, 8, some 7) ∧
    thinView08 (V08.thinDecode true 8 V08.wP) = some (0x1000, 8, some 7) ∧
    mrProvM Interp.TBM (V06.projBytes tbProv (V06.wP.take 1 ++ V06.wP256.drop 1)) =
      some (tbProv 7 7) ∧
    mrProvM Interp.TBM (V08.projBytes tbProv (V08.wP.take 1 ++ V08.wP256.drop 1)) =
      some (tbProv 7 7) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

theorem lockstep_parity_instance :
    V08.projBytes tbProv (V06.wP.map byte68) = V06.projBytes tbProv V06.wP ∧
    (Trusted.Rustc.V2026_08_01.MirSemantics.abstractBytesCoherentPtrProv? (V06.wP.map byte68)).isSome =
      (Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProv? V06.wP).isSome ∧
    thinView08 (V08.thinDecode true 8 (V06.wP.map byte68)) =
      thinView06 (V06.thinDecode true 8 V06.wP) ∧
    mrProvM Interp.TBM (V08.projBytes tbProv (V06.wP.map byte68)) =
      mrProvM Interp.TBM (V06.projBytes tbProv V06.wP) :=
  lockstep_parity (M := Interp.TBM) tbProv true 8 V06.wP

end Parity

/-! ## Axiom, import-isolation, and non-triviality audit -/

section AxiomAudit
open Lean Elab Command

/-- Verify that this module imports no `Anneal.*`, `Miri.*`, or `LeanMiriSpec.*`
module; that every declaration of this module depends only on the standard
axioms (`propext`, `Quot.sound`, `Classical.choice`) with zero `sorryAx` and
zero `Lean.ofReduceBool`; that no public theorem is trivial; and that the
headline theorems exist for both dialects. -/
elab "#assert_ptr_byte_coherence_mr_audit" : command => do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`Anneal).isPrefixOf modName || (`Miri).isPrefixOf modName ||
        (`LeanMiriSpec).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported"
  let rec isTrivialProp : Expr → Bool
    | .forallE _ _ body _ => isTrivialProp body
    | .letE _ _ _ body _ => isTrivialProp body
    | e =>
      if e.isConstOf ``True then true
      else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
      else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
      else false
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (c, ci) in env.constants.map₂.toList do
    if let .thmInfo v := ci then
      let u := (Lean.privateToUserName? c).getD c
      if !u.isInternal then
        if isTrivialProp v.type then
          throwError "{c} is a trivial theorem"
        theorems := theorems + 1
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool then throwError "{c} depends on Lean.ofReduceBool"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
  if checked == 0 then
    throwError "MiniRustSpec.PtrByteCoherenceMR: 0 declarations found"
  let perDialect : List String := [
    "coherent?_eq_some_iff", "coherent_decode_agreement",
    "trusted_coherent_implies_minirust_retains", "trusted_retains_implies_minirust_retains",
    "converse_gap_iff", "offset_splice_trusted_strips", "offset_splice_minirust_retains",
    "offset_splice_decode_divergence",
    "permuted_strips_trusted", "permuted_strips_minirust", "reversal_strips", "swap01_strips",
    "dupHead_strips", "w1_transforms_decode_strips",
    "mixed_provenance_strips_trusted", "mixed_provenance_strips_minirust",
    "missing_provenance_strips_trusted", "missing_provenance_strips_minirust",
    "uninit_rejected_trusted", "uninit_rejected_minirust", "proj_encodePtrBytes",
    "encodePtrM_proj", "encodePtr_proj", "decodePtrM_proj_encodePtrBytes",
    "thinDecode_encodePtrBytes", "decodePtrBytesNoForge_thin", "scalarLayoutPtr_coherent",
    "scalarLayoutPtr_incoherent", "scalarLayoutPtr_union_coherent",
    "scalarLayoutPtr_union_incoherent", "scalarLayoutNonPtr_strictUb_rejects_prov",
    "encodeUntyped_ptr", "encodeValueToBytes_thinPtr", "rawCarrier_roundtrip",
    "rawCarrier_ptr_roundtrip", "decodePtrBytesNoForge_slice", "decodePtrBytesNoForge_str",
    "decodePtrBytesNoForge_dyn", "slice_meta_with_provenance_rejected",
    "encodeWidePtrM_slice_proj", "encodeWidePtrM_dyn_proj",
    "coherent_wide_slice_decode_agreement", "coherent_wide_dyn_decode_agreement",
    "swapped_wide_slice_div",
    "minirust_bool_invalid", "minirust_u8_valid", "kani5205_bool_correspondence_M",
    "w_roundtrip", "w_ucg558_w1", "w_mixed_missing_uninit", "w_offset_splice_p_p4",
    "w_offset_splice_p_p256", "w_basic_memory_tag_blind", "w_wide_slice",
    "w_wide_swapped_halves", "w_wide_dyn", "w_kani5205_bool", "w_kani5205_char",
    "kani5205_char_divergence", "kani5205_char_divergence_instance",
    "kani5205_char_correspondence_M", "w_kani5205_char_enum_instance",
    "globalAlloc_reloc_correspondence_M", "w_mr_global_reloc_and_copyMemory",
    "w_kani5205_unaligned_and_maybeuninit",
    "coherent_decode_agreement_instance", "encode_roundtrip_instance",
    "rawCarrier_ptr_roundtrip_instance", "strip_laws_instance", "offset_splice_instance",
    "wide_and_bool_instance", "ep2_b1_mr_non_vacuity_instances", "ep2_b2_mr_non_vacuity_instances" ]
  let shared : List Lean.Name := [
    ``mrProvM_eq_some_iff, ``decodePtrProvenanceM_eq_some_iff, ``decodePtrM_eq,
    ``decodePtr_eq_M, ``decodePtrProvenance_eq_M, ``encodePtr_eq_M, ``encodePtrBytes_eq_M,
    ``endianness_encode_ptr, ``encodeWidePtrM_slice_eq, ``encodeWidePtrM_dyn_eq,
    ``decodeWidePtrM_slice_eq, ``decodeWidePtrM_dyn_eq, ``minirust_bool_decodeM_iff,
    ``minirust_u8_decodeM, ``minirust_bool_uninit_decodeM, ``minirust_u32_decodeM,
    ``minirust_char_decodeM_eq, ``minirust_char_decodeM_iff, ``minirust_char_uninit_decodeM,
    ``tbProv_inj, ``bmProv_eq_iff, ``coherent_parity, ``encode_parity,
    ``thinDecode_parity, ``lockstep_parity, ``w_lockstep_parity, ``lockstep_parity_instance ]
  let mut headline : Nat := 0
  for dialect in ["V06", "V08"] do
    for name in perDialect do
      let c := (`MiniRustSpec.PtrByteCoherenceMR).str dialect |>.str name
      match env.find? c with
      | some (.thmInfo _) => headline := headline + 1
      | _ => throwError "headline theorem {c} is missing"
  for c in shared do
    match env.find? c with
    | some (.thmInfo _) => headline := headline + 1
    | _ => throwError "headline theorem {c} is missing"
  logInfo m!"[PTR-BYTE-COHERENCE-MR-AUDIT] declarations={checked} theorems={theorems} headline={headline} ok=true"

#assert_ptr_byte_coherence_mr_audit

end AxiomAudit

end MiniRustSpec.PtrByteCoherenceMR
