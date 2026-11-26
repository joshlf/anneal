/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators
import Trusted.Rustc.V2026_08_01.MirSemantics.Terminators
import MiniRustSpec.Interp

/-!
# Prototype: pointer-byte fragment coherence (`UCG#558`, `rust#148259`) and read-time
untyped-byte validity (`Kani#5205`, `#5196`)

Off-`unstable` design spike for the paired TCB workstream. Nothing here modifies `trusted/`;
every divergence witness evaluates the real, unmodified live definitions.

## Findings against live `Trusted.Rustc.V2026_{06,08}_01.MirSemantics`

* **W1/W2 (permissive, unsound).** Live `AbstractByte.init (byte) (prov : Option (Nat × Nat))`
  records only `(allocId, tag)` per byte, so `abstractBytesUniformProv`,
  `decodePtrBytesNoForge` and `decodeScalarLayoutBytesNoForge` keep provenance on byte-reversed
  (8- and 4-byte), byte-swapped and byte-duplicated pointer images, and on same-`(allocId, tag)`
  offset splices (`p` / `p + 4`, `p` / `p + 256`). CTFE/Miri (`PointerFrag { idx, prov, bytes }`)
  strip all of them; MiniRust (`ProvenanceFrag { provenance, position }`) strips W1 but keeps
  W2, which is exactly the `UCG#558` tightening.
* **W3 (`tag`).** `ProvenancePtr` has no `tag` field (`ProvenancePtr.tag := allocId`); decode
  builds `{ allocId, offsetBytes }` and discards the byte pair's second component. Live
  encoders always write `(allocId, allocId)`, so honest round trips lose nothing, but a
  separately-tracked Tree Borrows tag cannot survive a byte round trip. Reversed `dyn` vtable
  halves keep vtable provenance (unsound); slice/`str` metadata with provenance is rejected.
* **`Kani#5205`.** Typed `bool` / `Unaligned<bool>` byte decodes fault at read time, and
  `MaybeUninit<bool>` holds `2u8`; but the active-frame `copy_nonoverlapping` into a `bool`
  local is premature UB, `write_bytes` is `.unsupported` on `bool` / `MaybeUninit<bool>` /
  `[u8; 1]`, and — permissive gaps — the untyped copy into `Unaligned<bool>` (and
  `MaybeUninit<Unaligned<bool>>`) stores an invalid `bool` field that later reads back as `2`
  without UB, and the foreign-frame copy stores `2u8` into a caller `bool` local unchecked.

## Prototype

Option 1 `AbstractByteProto.init (byte) (frag : Option PtrByteFragProto)` with
`PtrByteFragProto { allocId, tag, byteIdx, origOffset, ptrBytes }` (`origOffset` normalized
modulo `256 ^ ptrBytes = 2 ^ (8 * ptrBytes)`, equivalent to Miri's full `PointerFrag.bytes`
image), plus an Option 2 encoding (`AbstractByteOpt2`, defaulted fragment slot) with lossless
projections. Universal theorems cover intact round trips with exact `tag` (thin, slice/`str`,
`dyn`), in-order byte copies, stripping of every moved byte / reversal / swap / duplication /
offset or provenance splice / scalar-mixed / uninit / cross-width image, the Miri biconditional,
the MiniRust refinement (and its strict `UCG#558` tightening), and read-time-only validity.
-/

namespace Anneal.Proto.Ucg558PtrByteCoherenceProto

/-! ## 1. Little-endian byte images -/

/-- Little-endian image of the low `k` bytes of `bits`. -/
def leImage (bits : Nat) : Nat → List UInt8
  | 0 => []
  | k + 1 => UInt8.ofNat bits :: leImage (bits / 256) k

/-- Natural number denoted by little-endian bytes. -/
def leValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

theorem leImage_length (bits k : Nat) : (leImage bits k).length = k := by
  induction k generalizing bits with
  | zero => rfl
  | succ k ih => simp [leImage, ih]

theorem leValue_leImage (bits k : Nat) : leValue (leImage bits k) = bits % 256 ^ k := by
  induction k generalizing bits with
  | zero => show 0 = bits % 256 ^ 0; rw [Nat.pow_zero, Nat.mod_one]
  | succ k ih =>
    show (UInt8.ofNat bits).toNat + 256 * leValue (leImage (bits / 256) k) = _
    rw [show (UInt8.ofNat bits).toNat = bits % 256 from UInt8.toNat_ofNat', ih, Nat.pow_succ',
      Nat.mod_mul]

theorem leImage_getElem? (bits k i : Nat) :
    (leImage bits k)[i]? = if i < k then some (UInt8.ofNat (bits / 256 ^ i)) else none := by
  induction k generalizing bits i with
  | zero => simp [leImage]
  | succ k ih =>
    cases i with
    | zero => simp [leImage]
    | succ i =>
      simp only [leImage, List.getElem?_cons_succ, ih, Nat.div_div_eq_div_mul, Nat.pow_succ']
      simp [Nat.succ_lt_succ_iff]

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] {a b : α} (hc : c) :
    (if c then a else b) = a := by simp [hc]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] {a b : α} (hc : ¬c) :
    (if c then a else b) = b := by simp [hc]

/-! ## 2. Prototype representation -/

/-- Per-byte pointer fragment. -/
structure PtrByteFragProto : Type where
  allocId : Nat
  tag : Nat
  byteIdx : Nat
  origOffset : Nat
  ptrBytes : Nat
deriving DecidableEq

inductive AbstractByteProto : Type where
  | uninit : AbstractByteProto
  | init (byte : UInt8) (frag : Option PtrByteFragProto) : AbstractByteProto
deriving DecidableEq

structure ProvenancePtrProto : Type where
  allocId : Nat
  tag : Nat
  offsetBytes : Nat
deriving DecidableEq

def normOffset (ptrBytes off : Nat) : Nat := off % 256 ^ ptrBytes

def encodePtrFragsAux (allocId tag origOffset ptrBytes : Nat) :
    Nat → Nat → Nat → List AbstractByteProto
  | _, _, 0 => []
  | bits, idx, k + 1 =>
    .init (UInt8.ofNat bits) (some ⟨allocId, tag, idx, origOffset, ptrBytes⟩) ::
      encodePtrFragsAux allocId tag origOffset ptrBytes (bits / 256) (idx + 1) k

def encodePtrBytesProto (p : ProvenancePtrProto) (ptrBytes : Nat) : List AbstractByteProto :=
  encodePtrFragsAux p.allocId p.tag (normOffset ptrBytes p.offsetBytes) ptrBytes
    (normOffset ptrBytes p.offsetBytes) 0 ptrBytes

def fragsCoherentFrom (allocId tag origOffset ptrBytes : Nat) :
    Nat → List AbstractByteProto → Bool
  | _, [] => true
  | idx, .init _ (some f) :: rest =>
    (Nat.beq f.allocId allocId && Nat.beq f.tag tag && Nat.beq f.byteIdx idx &&
      Nat.beq f.origOffset origOffset && Nat.beq f.ptrBytes ptrBytes) &&
      fragsCoherentFrom allocId tag origOffset ptrBytes (idx + 1) rest
  | _, _ => false

def dataBytesProto : List AbstractByteProto → Option (List UInt8)
  | [] => some []
  | .uninit :: _ => none
  | .init b _ :: rest =>
    match dataBytesProto rest with
    | some bs => some (b :: bs)
    | none => none

def abstractBytesCoherentPtrProvProto (ptrBytes : Nat) :
    List AbstractByteProto → Option ProvenancePtrProto
  | [] => none
  | .uninit :: _ => none
  | .init _ none :: _ => none
  | .init b (some f) :: rest =>
    match
      fragsCoherentFrom f.allocId f.tag f.origOffset ptrBytes 0 (.init b (some f) :: rest) &&
        Nat.beq (rest.length + 1) ptrBytes,
      dataBytesProto (.init b (some f) :: rest)
    with
    | true, some data =>
      match Nat.beq (leValue data) f.origOffset with
      | true => some ⟨f.allocId, f.tag, f.origOffset⟩
      | false => none
    | _, _ => none

/-! ## 3. Core lemmas -/

theorem encodePtrFragsAux_length (a t o n bits idx k : Nat) :
    (encodePtrFragsAux a t o n bits idx k).length = k := by
  induction k generalizing bits idx with
  | zero => rfl
  | succ k ih => simp [encodePtrFragsAux, ih]

theorem encodePtrFragsAux_getElem? (a t o n bits idx k i : Nat) :
    (encodePtrFragsAux a t o n bits idx k)[i]? =
      if i < k then
        some (.init (UInt8.ofNat (bits / 256 ^ i)) (some ⟨a, t, idx + i, o, n⟩))
      else none := by
  induction k generalizing bits idx i with
  | zero => simp [encodePtrFragsAux]
  | succ k ih =>
    cases i with
    | zero => simp [encodePtrFragsAux]
    | succ i =>
      simp only [encodePtrFragsAux, List.getElem?_cons_succ, ih, Nat.div_div_eq_div_mul,
        Nat.pow_succ']
      simp [Nat.succ_lt_succ_iff, Nat.add_assoc, Nat.add_comm 1 i]

theorem fragsCoherentFrom_encode (a t o n bits idx k : Nat) :
    fragsCoherentFrom a t o n idx (encodePtrFragsAux a t o n bits idx k) = true := by
  induction k generalizing bits idx with
  | zero => rfl
  | succ k ih => simp [encodePtrFragsAux, fragsCoherentFrom, ih]

theorem dataBytesProto_encode (a t o n bits idx k : Nat) :
    dataBytesProto (encodePtrFragsAux a t o n bits idx k) = some (leImage bits k) := by
  induction k generalizing bits idx with
  | zero => rfl
  | succ k ih => simp [encodePtrFragsAux, dataBytesProto, ih, leImage]

/-- Characterization: coherent fragments pin every byte's full fragment. -/
theorem fragsCoherentFrom_getElem? (a t o n : Nat) :
    ∀ (l : List AbstractByteProto) (idx : Nat),
      fragsCoherentFrom a t o n idx l = true →
      ∀ (i : Nat) (x : AbstractByteProto), l[i]? = some x →
        ∃ b, x = .init b (some ⟨a, t, idx + i, o, n⟩) := by
  intro l
  induction l with
  | nil => intro idx _ i x hx; simp at hx
  | cons y rest ih =>
    intro idx h i x hx
    cases y with
    | uninit => simp [fragsCoherentFrom] at h
    | init b fo =>
      cases fo with
      | none => simp [fragsCoherentFrom] at h
      | some f =>
        simp only [fragsCoherentFrom, Bool.and_eq_true, Nat.beq_eq] at h
        obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hr⟩ := h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          refine ⟨b, ?_⟩
          cases f
          simp only at h1 h2 h3 h4 h5
          subst h1 h2 h3 h4 h5
          rfl
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx
          obtain ⟨b', hb'⟩ := ih (idx + 1) hr i x hx
          refine ⟨b', ?_⟩
          rw [hb', Nat.add_assoc, Nat.add_comm 1 i]

theorem coherent_some_frags (n : Nat) (l : List AbstractByteProto) (p : ProvenancePtrProto)
    (h : abstractBytesCoherentPtrProvProto n l = some p) :
    l.length = n ∧
    ∀ (i : Nat) (x : AbstractByteProto), l[i]? = some x →
      ∃ b, x = .init b (some ⟨p.allocId, p.tag, i, p.offsetBytes, n⟩) := by
  cases l with
  | nil => simp [abstractBytesCoherentPtrProvProto] at h
  | cons y rest =>
    cases y with
    | uninit => simp [abstractBytesCoherentPtrProvProto] at h
    | init b fo =>
      cases fo with
      | none => simp [abstractBytesCoherentPtrProvProto] at h
      | some f =>
        simp only [abstractBytesCoherentPtrProvProto] at h
        cases hc : fragsCoherentFrom f.allocId f.tag f.origOffset n 0 (.init b (some f) :: rest)
          <;> cases hl : Nat.beq (rest.length + 1) n
          <;> cases hd : dataBytesProto (.init b (some f) :: rest)
          <;> simp only [hc, hl, hd, Bool.and_self, Bool.and_false, Bool.false_and] at h
          <;> try (simp at h)
        rename_i data
        cases hv : Nat.beq (leValue data) f.origOffset <;> simp only [hv] at h
        · simp at h
        · simp only [Option.some.injEq] at h
          subst h
          refine ⟨?_, ?_⟩
          · simpa using Nat.eq_of_beq_eq_true hl
          · intro i x hx
            obtain ⟨b', hb'⟩ := fragsCoherentFrom_getElem? _ _ _ _ _ 0 hc i x hx
            exact ⟨b', by simpa using hb'⟩

/-- **Intact round-trip (universal).** -/
theorem coherent_encode (p : ProvenancePtrProto) (n : Nat) (hn : 0 < n) :
    abstractBytesCoherentPtrProvProto n (encodePtrBytesProto p n) =
      some ⟨p.allocId, p.tag, normOffset n p.offsetBytes⟩ := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ k =>
    have hc := fragsCoherentFrom_encode p.allocId p.tag (normOffset (k + 1) p.offsetBytes) (k + 1)
      (normOffset (k + 1) p.offsetBytes) 0 (k + 1)
    have hd := dataBytesProto_encode p.allocId p.tag (normOffset (k + 1) p.offsetBytes) (k + 1)
      (normOffset (k + 1) p.offsetBytes) 0 (k + 1)
    have hlt : normOffset (k + 1) p.offsetBytes < 256 ^ (k + 1) :=
      Nat.mod_lt _ (Nat.pow_pos (by decide))
    simp only [encodePtrBytesProto, encodePtrFragsAux] at hc hd ⊢
    simp only [abstractBytesCoherentPtrProvProto, hc, hd, encodePtrFragsAux_length,
      Nat.beq_refl, Bool.and_self, leValue_leImage, Nat.mod_eq_of_lt hlt]

/-! ## 4. Universal provenance-stripping theorems -/

theorem coherent_none_of_byteIdx_ne (n : Nat) (l : List AbstractByteProto) (i : Nat) (b : UInt8)
    (f : PtrByteFragProto) (hx : l[i]? = some (.init b (some f))) (hne : f.byteIdx ≠ i) :
    abstractBytesCoherentPtrProvProto n l = none := by
  cases h : abstractBytesCoherentPtrProvProto n l with
  | none => rfl
  | some p =>
    obtain ⟨_, hall⟩ := coherent_some_frags n l p h
    obtain ⟨b', hb⟩ := hall i _ hx
    simp only [AbstractByteProto.init.injEq, Option.some.injEq] at hb
    obtain ⟨_, rfl⟩ := hb
    exact absurd rfl hne

theorem coherent_none_of_ptrBytes_ne (n : Nat) (l : List AbstractByteProto) (i : Nat) (b : UInt8)
    (f : PtrByteFragProto) (hx : l[i]? = some (.init b (some f))) (hne : f.ptrBytes ≠ n) :
    abstractBytesCoherentPtrProvProto n l = none := by
  cases h : abstractBytesCoherentPtrProvProto n l with
  | none => rfl
  | some p =>
    obtain ⟨_, hall⟩ := coherent_some_frags n l p h
    obtain ⟨b', hb⟩ := hall i _ hx
    simp only [AbstractByteProto.init.injEq, Option.some.injEq] at hb
    obtain ⟨_, rfl⟩ := hb
    exact absurd rfl hne

theorem coherent_none_of_no_frag (n : Nat) (l : List AbstractByteProto) (i : Nat) (b : UInt8)
    (hx : l[i]? = some (.init b none)) :
    abstractBytesCoherentPtrProvProto n l = none := by
  cases h : abstractBytesCoherentPtrProvProto n l with
  | none => rfl
  | some p =>
    obtain ⟨_, hall⟩ := coherent_some_frags n l p h
    obtain ⟨b', hb⟩ := hall i _ hx
    simp at hb

theorem coherent_none_of_uninit (n : Nat) (l : List AbstractByteProto) (i : Nat)
    (hx : l[i]? = some .uninit) :
    abstractBytesCoherentPtrProvProto n l = none := by
  cases h : abstractBytesCoherentPtrProvProto n l with
  | none => rfl
  | some p =>
    obtain ⟨_, hall⟩ := coherent_some_frags n l p h
    obtain ⟨b', hb⟩ := hall i _ hx
    simp at hb

/-- Two fragments with distinct `(allocId, tag, origOffset)` never cohere. -/
theorem coherent_none_of_frag_mismatch (n : Nat) (l : List AbstractByteProto) (i j : Nat)
    (b b' : UInt8) (f g : PtrByteFragProto)
    (hi : l[i]? = some (.init b (some f))) (hj : l[j]? = some (.init b' (some g)))
    (hne : (f.allocId, f.tag, f.origOffset) ≠ (g.allocId, g.tag, g.origOffset)) :
    abstractBytesCoherentPtrProvProto n l = none := by
  cases h : abstractBytesCoherentPtrProvProto n l with
  | none => rfl
  | some p =>
    obtain ⟨_, hall⟩ := coherent_some_frags n l p h
    obtain ⟨c, hc⟩ := hall i _ hi
    obtain ⟨c', hc'⟩ := hall j _ hj
    simp only [AbstractByteProto.init.injEq, Option.some.injEq] at hc hc'
    obtain ⟨_, rfl⟩ := hc
    obtain ⟨_, rfl⟩ := hc'
    exact absurd rfl hne

theorem encodePtrBytesProto_getElem? (p : ProvenancePtrProto) (n i : Nat) (hi : i < n) :
    (encodePtrBytesProto p n)[i]? =
      some (.init (UInt8.ofNat (normOffset n p.offsetBytes / 256 ^ i))
        (some ⟨p.allocId, p.tag, i, normOffset n p.offsetBytes, n⟩)) := by
  simp [encodePtrBytesProto, encodePtrFragsAux_getElem?, hi]

theorem encodePtrBytesProto_length (p : ProvenancePtrProto) (n : Nat) :
    (encodePtrBytesProto p n).length = n := by
  simp [encodePtrBytesProto, encodePtrFragsAux_length]

/-- **Moved-byte stripping (universal).** Any byte list holding, at position `i`, the encoded
byte `j ≠ i` of an intact pointer image is stripped: covers every non-identity permutation,
byte reversal, byte swaps, and duplication. -/
theorem coherent_none_of_moved_byte (p : ProvenancePtrProto) (n : Nat) (l : List AbstractByteProto)
    (i j : Nat) (hj : j < n) (hji : j ≠ i) (h : l[i]? = (encodePtrBytesProto p n)[j]?) :
    abstractBytesCoherentPtrProvProto n l = none := by
  rw [encodePtrBytesProto_getElem? p n j hj] at h
  exact coherent_none_of_byteIdx_ne n l i _ _ h hji

/-- Swap the first two bytes. -/
def swapFirstTwo {α : Type} : List α → List α
  | a :: b :: rest => b :: a :: rest
  | l => l

/-- Repeat byte `0` across the whole image. -/
def dupFirstByte {α : Type} : List α → List α
  | [] => []
  | x :: rest => List.replicate (rest.length + 1) x

/-- Byte `0 .. k` of `l₁` followed by bytes `k ..` of `l₂`. -/
def spliceBytes {α : Type} (k : Nat) (l₁ l₂ : List α) : List α :=
  l₁.take k ++ l₂.drop k

/-- Apply an index map `σ` to a byte image (`σ i` must lie in range for a permutation). -/
def permuteBytes (σ : Nat → Nat) (l : List AbstractByteProto) : List AbstractByteProto :=
  (List.range l.length).map (fun i => (l[σ i]?).getD .uninit)

theorem two_le_iff_exists (n : Nat) (h : 2 ≤ n) : ∃ m, n = m + 2 :=
  ⟨n - 2, (Nat.sub_add_cancel h).symm⟩

/-- **Byte reversal strips provenance (universal, `ptrBytes ≥ 2`, every offset incl. `0`).** -/
theorem coherent_reverse_none (p : ProvenancePtrProto) (n : Nat) (hn : 2 ≤ n) :
    abstractBytesCoherentPtrProvProto n (encodePtrBytesProto p n).reverse = none := by
  obtain ⟨m, rfl⟩ := two_le_iff_exists n hn
  apply coherent_none_of_moved_byte p (m + 2) _ 0 (m + 1) (Nat.lt_succ_self _)
    (Nat.succ_ne_zero m)
  rw [List.getElem?_reverse (by simp [encodePtrBytesProto_length]),
    encodePtrBytesProto_length]
  rfl

/-- **Swapping bytes `0` and `1` strips provenance (universal, `ptrBytes ≥ 2`).** -/
theorem coherent_swap01_none (p : ProvenancePtrProto) (n : Nat) (hn : 2 ≤ n) :
    abstractBytesCoherentPtrProvProto n (swapFirstTwo (encodePtrBytesProto p n)) = none := by
  obtain ⟨m, rfl⟩ := two_le_iff_exists n hn
  apply coherent_none_of_moved_byte p (m + 2) _ 0 1 (by simp) (by decide)
  simp only [encodePtrBytesProto, encodePtrFragsAux, swapFirstTwo]
  rfl

/-- **Duplicating byte `0` strips provenance (universal, `ptrBytes ≥ 2`).** -/
theorem coherent_dup_none (p : ProvenancePtrProto) (n : Nat) (hn : 2 ≤ n) :
    abstractBytesCoherentPtrProvProto n (dupFirstByte (encodePtrBytesProto p n)) = none := by
  obtain ⟨m, rfl⟩ := two_le_iff_exists n hn
  apply coherent_none_of_moved_byte p (m + 2) _ 1 0 (by simp) (by decide)
  simp only [encodePtrBytesProto, encodePtrFragsAux, dupFirstByte, List.length_cons,
    encodePtrFragsAux_length, List.replicate_succ, List.getElem?_cons_succ,
    List.getElem?_cons_zero]

/-- **Every non-identity index map strips provenance (universal).** -/
theorem coherent_permute_none (p : ProvenancePtrProto) (n : Nat) (σ : Nat → Nat) (i : Nat)
    (hi : i < n) (hσ : σ i < n) (hne : σ i ≠ i) :
    abstractBytesCoherentPtrProvProto n (permuteBytes σ (encodePtrBytesProto p n)) = none := by
  apply coherent_none_of_moved_byte p n _ i (σ i) hσ hne
  have hl := encodePtrBytesProto_length p n
  simp only [permuteBytes, List.getElem?_map, List.getElem?_range, hl, hi,
    Option.map_some, encodePtrBytesProto_getElem? p n (σ i) hσ, Option.getD_some]

/-- **Offset / provenance splicing strips provenance (universal).** Prefix `0 .. k` of `p₁`
followed by suffix `k ..` of `p₂` (`0 < k < ptrBytes`) is stripped whenever the two pointers
differ in `allocId`, `tag`, or normalized offset — in particular for same-`(allocId, tag)`
pointers `p` and `p + 256` whose byte `0` is identical. -/
theorem coherent_splice_none (p₁ p₂ : ProvenancePtrProto) (n k : Nat) (hk0 : 0 < k) (hkn : k < n)
    (hne : (p₁.allocId, p₁.tag, normOffset n p₁.offsetBytes) ≠
      (p₂.allocId, p₂.tag, normOffset n p₂.offsetBytes)) :
    abstractBytesCoherentPtrProvProto n
      (spliceBytes k (encodePtrBytesProto p₁ n) (encodePtrBytesProto p₂ n)) = none := by
  have hl₁ := encodePtrBytesProto_length p₁ n
  have hlt : (List.take k (encodePtrBytesProto p₁ n)).length = k := by
    simp [hl₁, Nat.min_eq_left (Nat.le_of_lt hkn)]
  have h0 : (spliceBytes k (encodePtrBytesProto p₁ n) (encodePtrBytesProto p₂ n))[0]? =
      (encodePtrBytesProto p₁ n)[0]? := by
    rw [spliceBytes, List.getElem?_append_left (by rw [hlt]; exact hk0), List.getElem?_take]
    simp [hk0]
  have hk : (spliceBytes k (encodePtrBytesProto p₁ n) (encodePtrBytesProto p₂ n))[k]? =
      (encodePtrBytesProto p₂ n)[k]? := by
    rw [spliceBytes, List.getElem?_append_right (by rw [hlt]; exact Nat.le_refl k), hlt,
      List.getElem?_drop, Nat.sub_self, Nat.add_zero]
  rw [encodePtrBytesProto_getElem? p₁ n 0 (Nat.lt_trans hk0 hkn)] at h0
  rw [encodePtrBytesProto_getElem? p₂ n k hkn] at hk
  exact coherent_none_of_frag_mismatch n _ 0 k _ _ _ _ h0 hk hne

/-- **Mixed pointer/integer bytes strip (universal):** replacing any byte by a plain integer byte. -/
theorem coherent_set_plain_none (p : ProvenancePtrProto) (n k : Nat) (b : UInt8) (hk : k < n) :
    abstractBytesCoherentPtrProvProto n ((encodePtrBytesProto p n).set k (.init b none)) = none :=
  coherent_none_of_no_frag n _ k b
    (List.getElem?_set_self (by rw [encodePtrBytesProto_length]; exact hk))

/-- **Uninitialized byte strips (universal).** -/
theorem coherent_set_uninit_none (p : ProvenancePtrProto) (n k : Nat) (hk : k < n) :
    abstractBytesCoherentPtrProvProto n ((encodePtrBytesProto p n).set k .uninit) = none :=
  coherent_none_of_uninit n _ k
    (List.getElem?_set_self (by rw [encodePtrBytesProto_length]; exact hk))

/-- **Cross-width splicing strips (universal):** two `m`-byte images read as one `2m`-byte
pointer (e.g. two 32-bit fragments read as a 64-bit pointer). -/
theorem coherent_cross_width_none (p q : ProvenancePtrProto) (m : Nat) (hm : 0 < m) :
    abstractBytesCoherentPtrProvProto (m + m) (encodePtrBytesProto p m ++ encodePtrBytesProto q m)
      = none := by
  have h0 : (encodePtrBytesProto p m ++ encodePtrBytesProto q m)[0]? =
      (encodePtrBytesProto p m)[0]? :=
    List.getElem?_append_left (by rw [encodePtrBytesProto_length]; exact hm)
  rw [encodePtrBytesProto_getElem? p m 0 hm] at h0
  exact coherent_none_of_ptrBytes_ne (m + m) _ 0 _ _ h0
    (Nat.ne_of_lt (Nat.lt_add_of_pos_right hm))

/-! ## 5. Values, wide pointers, scalar layouts and typed decoding -/

/-- Pointee shape of a pointer type. -/
inductive PointeeProto : Type where
  | thin : PointeeProto
  | slice : PointeeProto
  | str : PointeeProto
  | dyn : PointeeProto
deriving DecidableEq

/-- Prototype runtime value; `ptr` keeps the Tree Borrows `tag` separately from `allocId`. -/
inductive ValueProto : Type where
  | scalar (bits sizeBytes : Nat) : ValueProto
  | ptr (p : ProvenancePtrProto) (sizeBytes : Nat) : ValueProto
  | aggregate (fields : List ValueProto) : ValueProto
  | rawBytes (bytes : List AbstractByteProto) : ValueProto

/-- Plain little-endian integer bytes (no fragments). -/
def encodeLittleEndianBytesProto (bits n : Nat) : List AbstractByteProto :=
  (leImage bits n).map (fun b => .init b none)

def abstractBytesHaveFragProto : List AbstractByteProto → Bool
  | [] => false
  | .init _ (some _) :: _ => true
  | _ :: rest => abstractBytesHaveFragProto rest

/-- Thin pointer decode without forging provenance. -/
def decodeThinPtrBytesProto (isRef : Bool) (ptrBytes : Nat) (bytes : List AbstractByteProto) :
    Option ValueProto :=
  match Nat.beq bytes.length ptrBytes, dataBytesProto bytes with
  | true, some data =>
    match abstractBytesCoherentPtrProvProto ptrBytes bytes with
    | some p => some (.ptr p ptrBytes)
    | none =>
      match isRef with
      | true => none
      | false => some (.scalar (leValue data) ptrBytes)
  | _, _ => none

/-- Wide pointer decode: data half as a thin pointer; slice/`str` metadata must be a plain
integer; `dyn` metadata is a vtable pointer that must itself be coherent for references. -/
def decodeWidePtrBytesProto (isRef isDyn : Bool) (ptrBytes : Nat) (bytes : List AbstractByteProto) :
    Option ValueProto :=
  match Nat.beq bytes.length (ptrBytes + ptrBytes) with
  | false => none
  | true =>
    let metaBytes := bytes.drop ptrBytes
    let metaOpt : Option ValueProto :=
      match isDyn with
      | true => decodeThinPtrBytesProto isRef ptrBytes metaBytes
      | false =>
        match abstractBytesHaveFragProto metaBytes, dataBytesProto metaBytes with
        | false, some md => some (.scalar (leValue md) ptrBytes)
        | _, _ => none
    match decodeThinPtrBytesProto isRef ptrBytes (bytes.take ptrBytes), metaOpt with
    | some d, some m => some (.aggregate [d, m])
    | _, _ => none

def decodePtrBytesNoForgeProto (isRef : Bool) (pointee : PointeeProto) (ptrBytes : Nat)
    (bytes : List AbstractByteProto) : Option ValueProto :=
  match pointee with
  | .thin => decodeThinPtrBytesProto isRef ptrBytes bytes
  | .slice => decodeWidePtrBytesProto isRef false ptrBytes bytes
  | .str => decodeWidePtrBytesProto isRef false ptrBytes bytes
  | .dyn => decodeWidePtrBytesProto isRef true ptrBytes bytes

/-- Prototype type language: integers, `bool`, `char`, thin/wide raw pointers and references,
function pointers, arrays, `MaybeUninit<T>` (untyped union payload) and `Unaligned<T>`
(`#[repr(packed)]` single-field struct). -/
inductive TyProto : Type where
  | uint (sizeBytes : Nat) : TyProto
  | bool : TyProto
  | char : TyProto
  | rawPtr (pointee : PointeeProto) : TyProto
  | ref (pointee : PointeeProto) : TyProto
  | fnPtr : TyProto
  | array (elem : TyProto) (len : Nat) : TyProto
  | maybeUninit (inner : TyProto) : TyProto
  | unaligned (inner : TyProto) : TyProto

def PointeeProto.width (ptrBytes : Nat) : PointeeProto → Nat
  | .thin => ptrBytes
  | _ => ptrBytes + ptrBytes

def TyProto.sizeBytes (ptrBytes : Nat) : TyProto → Nat
  | .uint n => n
  | .bool => 1
  | .char => 4
  | .rawPtr pt => pt.width ptrBytes
  | .ref pt => pt.width ptrBytes
  | .fnPtr => ptrBytes
  | .array elem len => elem.sizeBytes ptrBytes * len
  | .maybeUninit inner => inner.sizeBytes ptrBytes
  | .unaligned inner => inner.sizeBytes ptrBytes

/-- Encode a list of element values with `enc`, concatenating the images. -/
def encodeListProto (enc : ValueProto → Option (List AbstractByteProto)) :
    List ValueProto → Option (List AbstractByteProto)
  | [] => some []
  | v :: vs =>
    match enc v, encodeListProto enc vs with
    | some b, some bs => some (b ++ bs)
    | _, _ => none

/-- Thin pointer-typed value encoding (`.ptr` carries fragments; raw `.scalar` does not). -/
def encodeThinPtrValueProto (allowScalar : Bool) (ptrBytes : Nat) : ValueProto →
    Option (List AbstractByteProto)
  | .ptr p sz =>
    match Nat.beq sz ptrBytes with
    | true => some (encodePtrBytesProto p ptrBytes)
    | false => none
  | .scalar bits sz =>
    match allowScalar && Nat.beq sz ptrBytes with
    | true => some (encodeLittleEndianBytesProto bits ptrBytes)
    | false => none
  | _ => none

def encodePtrValueProto (isRaw : Bool) (ptrBytes : Nat) : PointeeProto → ValueProto →
    Option (List AbstractByteProto)
  | .thin, v => encodeThinPtrValueProto isRaw ptrBytes v
  | .dyn, .aggregate [d, vt] =>
    match encodeThinPtrValueProto isRaw ptrBytes d, encodeThinPtrValueProto isRaw ptrBytes vt with
    | some db, some vb => some (db ++ vb)
    | _, _ => none
  | .dyn, _ => none
  | _, .aggregate [d, .scalar len _] =>
    match encodeThinPtrValueProto isRaw ptrBytes d with
    | some db => some (db ++ encodeLittleEndianBytesProto len ptrBytes)
    | none => none
  | _, _ => none

/-- Typed encoder (thin, `fnPtr`, wide slice/`str`, and wide `dyn` with vtable fragments). -/
def encodeValueToBytesProto (ptrBytes : Nat) : TyProto → ValueProto →
    Option (List AbstractByteProto)
  | .uint n, .scalar bits sz =>
    match Nat.beq sz n && Nat.blt bits (256 ^ n) with
    | true => some (encodeLittleEndianBytesProto bits n)
    | false => none
  | .bool, .scalar bits sz =>
    match Nat.beq sz 1 && Nat.ble bits 1 with
    | true => some (encodeLittleEndianBytesProto bits 1)
    | false => none
  | .char, .scalar bits sz =>
    match Nat.beq sz 4 &&
        Trusted.Rustc.V2026_06_01.MirSemantics.isValidCharCode bits with
    | true => some (encodeLittleEndianBytesProto bits 4)
    | false => none
  | .rawPtr pt, v => encodePtrValueProto true ptrBytes pt v
  | .ref pt, v => encodePtrValueProto false ptrBytes pt v
  | .fnPtr, v => encodeThinPtrValueProto false ptrBytes v
  | .array elem len, .aggregate vs =>
    match Nat.beq vs.length len with
    | true => encodeListProto (encodeValueToBytesProto ptrBytes elem) vs
    | false => none
  | .maybeUninit inner, .rawBytes bs =>
    match Nat.beq bs.length (inner.sizeBytes ptrBytes) with
    | true => some bs
    | false => none
  | .maybeUninit inner, v => encodeValueToBytesProto ptrBytes inner v
  | .unaligned inner, .aggregate [v] => encodeValueToBytesProto ptrBytes inner v
  | _, _ => none

/-- Decode `count` chunks of `sz` bytes with `dec`. -/
def decodeChunksProto (dec : List AbstractByteProto → Option ValueProto) (sz : Nat) :
    Nat → List AbstractByteProto → Option (List ValueProto)
  | 0, [] => some []
  | 0, _ :: _ => none
  | k + 1, bytes =>
    match dec (bytes.take sz), decodeChunksProto dec sz k (bytes.drop sz) with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- Plain integer decode: exact width, initialized, no fragments. -/
def decodePlainIntProto (n : Nat) (bytes : List AbstractByteProto) : Option ValueProto :=
  match Nat.beq bytes.length n && !abstractBytesHaveFragProto bytes, dataBytesProto bytes with
  | true, some data => some (.scalar (leValue data) n)
  | _, _ => none

/-- **Read-time typed decoder.** Validity (`bool ∈ {0, 1}`, `char` scalar values, reference
provenance) is checked here, at read time; `MaybeUninit<T>` reads never inspect bytes. -/
def decodeTypedValueFromBytesProto (ptrBytes : Nat) : TyProto → List AbstractByteProto →
    Option ValueProto
  | .uint n, bytes => decodePlainIntProto n bytes
  | .bool, bytes =>
    match decodePlainIntProto 1 bytes with
    | some (.scalar v 1) =>
      match Nat.ble v 1 with
      | true => some (.scalar v 1)
      | false => none
    | _ => none
  | .char, bytes =>
    match decodePlainIntProto 4 bytes with
    | some (.scalar v 4) =>
      match Trusted.Rustc.V2026_06_01.MirSemantics.isValidCharCode v with
      | true => some (.scalar v 4)
      | false => none
    | _ => none
  | .rawPtr pt, bytes => decodePtrBytesNoForgeProto false pt ptrBytes bytes
  | .ref pt, bytes => decodePtrBytesNoForgeProto true pt ptrBytes bytes
  | .fnPtr, bytes => decodePtrBytesNoForgeProto true .thin ptrBytes bytes
  | .array elem len, bytes =>
    match Nat.beq bytes.length (elem.sizeBytes ptrBytes * len) with
    | false => none
    | true =>
      match decodeChunksProto (decodeTypedValueFromBytesProto ptrBytes elem)
          (elem.sizeBytes ptrBytes) len bytes with
      | some vs => some (.aggregate vs)
      | none => none
  | .maybeUninit inner, bytes =>
    match Nat.beq bytes.length (inner.sizeBytes ptrBytes) with
    | true => some (.rawBytes bytes)
    | false => none
  | .unaligned inner, bytes =>
    match decodeTypedValueFromBytesProto ptrBytes inner bytes with
    | some v => some (.aggregate [v])
    | none => none

/-- Width of a live `ScalarLayout` at pointer width `ptrBytes`. -/
def scalarLayoutWidthProto (ptrBytes : Nat) :
    Trusted.Rustc.V2026_06_01.Layout.ScalarLayout → Option Nat
  | .initialized (.pointer _) _ => some ptrBytes
  | .union (.pointer _) => some ptrBytes
  | sl => Trusted.Rustc.V2026_06_01.MirSemantics.scalarLayoutByteWidth sl

/-- Prototype of live `decodeScalarLayoutBytesNoForge` with fragment-coherent pointers. -/
def decodeScalarLayoutBytesNoForgeProto (ptrBytes : Nat)
    (sl : Trusted.Rustc.V2026_06_01.Layout.ScalarLayout) (bytes : List AbstractByteProto) :
    Option ValueProto :=
  match scalarLayoutWidthProto ptrBytes sl with
  | none => none
  | some sz =>
    match Nat.beq bytes.length sz, dataBytesProto bytes with
    | true, some data =>
      match sl with
      | .initialized (.pointer _) vr =>
        match abstractBytesCoherentPtrProvProto sz bytes with
        | some p => some (.ptr p sz)
        | none =>
          match Trusted.Rustc.V2026_06_01.MirSemantics.wrappingRangeContains vr (leValue data) with
          | true => some (.scalar (leValue data) sz)
          | false => none
      | .union (.pointer _) =>
        match abstractBytesCoherentPtrProvProto sz bytes with
        | some p => some (.ptr p sz)
        | none => some (.scalar (leValue data) sz)
      | .initialized _ vr =>
        match abstractBytesHaveFragProto bytes,
          Trusted.Rustc.V2026_06_01.MirSemantics.wrappingRangeContains vr (leValue data) with
        | false, true =>
          match Nat.beq sz 4 && Nat.beq vr.start 0 && Nat.beq vr.end_ 0x10FFFF with
          | true =>
            match Trusted.Rustc.V2026_06_01.MirSemantics.isValidCharCode (leValue data) with
            | true => some (.scalar (leValue data) sz)
            | false => none
          | false => some (.scalar (leValue data) sz)
        | _, _ => none
      | .union _ =>
        match abstractBytesHaveFragProto bytes with
        | false => some (.scalar (leValue data) sz)
        | true => none
    | _, _ => none

/-! ### Universal value-level round trips -/

theorem decodeThin_encode (isRef : Bool) (p : ProvenancePtrProto) (n : Nat) (hn : 0 < n) :
    decodeThinPtrBytesProto isRef n (encodePtrBytesProto p n) =
      some (.ptr ⟨p.allocId, p.tag, normOffset n p.offsetBytes⟩ n) := by
  have hd := dataBytesProto_encode p.allocId p.tag (normOffset n p.offsetBytes) n
    (normOffset n p.offsetBytes) 0 n
  simp only [decodeThinPtrBytesProto, encodePtrBytesProto_length, Nat.beq_refl,
    coherent_encode p n hn]
  simp only [encodePtrBytesProto] at hd ⊢
  simp only [hd]

/-- **Intact thin round-trip with exact tag (universal).** -/
theorem decode_encode_thin_exact (isRef : Bool) (p : ProvenancePtrProto) (n : Nat) (hn : 0 < n)
    (hoff : p.offsetBytes < 256 ^ n) :
    decodePtrBytesNoForgeProto isRef .thin n (encodePtrBytesProto p n) = some (.ptr p n) := by
  simp only [decodePtrBytesNoForgeProto, decodeThin_encode isRef p n hn, normOffset,
    Nat.mod_eq_of_lt hoff]

theorem take_append_of_length {α : Type} (l₁ l₂ : List α) (n : Nat) (h : l₁.length = n) :
    (l₁ ++ l₂).take n = l₁ := by
  subst h; simp

theorem drop_append_of_length {α : Type} (l₁ l₂ : List α) (n : Nat) (h : l₁.length = n) :
    (l₁ ++ l₂).drop n = l₂ := by
  subst h; simp

/-- **Intact wide `dyn` round-trip (universal):** data and vtable halves both recovered with
exact `allocId`, `tag` and offset. -/
theorem decode_encode_dyn_exact (isRef : Bool) (p vt : ProvenancePtrProto) (n : Nat) (hn : 0 < n)
    (hp : p.offsetBytes < 256 ^ n) (hvt : vt.offsetBytes < 256 ^ n) :
    decodePtrBytesNoForgeProto isRef .dyn n (encodePtrBytesProto p n ++ encodePtrBytesProto vt n) =
      some (.aggregate [.ptr p n, .ptr vt n]) := by
  have hl := encodePtrBytesProto_length p n
  have hl' := encodePtrBytesProto_length vt n
  simp only [decodePtrBytesNoForgeProto, decodeWidePtrBytesProto, List.length_append, hl, hl',
    Nat.beq_refl, take_append_of_length _ _ n hl, drop_append_of_length _ _ n hl,
    decodeThin_encode isRef _ n hn, normOffset, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hvt]

theorem dataBytesProto_plain (bits n : Nat) :
    dataBytesProto (encodeLittleEndianBytesProto bits n) = some (leImage bits n) := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
    simp only [encodeLittleEndianBytesProto, leImage, List.map_cons] at ih ⊢
    simp only [dataBytesProto, ih]

theorem haveFrag_plain (bits n : Nat) :
    abstractBytesHaveFragProto (encodeLittleEndianBytesProto bits n) = false := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
    simp only [encodeLittleEndianBytesProto, leImage, List.map_cons] at ih ⊢
    simp only [abstractBytesHaveFragProto, ih]

theorem plain_length (bits n : Nat) : (encodeLittleEndianBytesProto bits n).length = n := by
  simp [encodeLittleEndianBytesProto, leImage_length]

/-- **Intact wide slice/`str` round-trip (universal).** -/
theorem decode_encode_slice_exact (isRef : Bool) (p : ProvenancePtrProto) (len n : Nat)
    (hn : 0 < n) (hp : p.offsetBytes < 256 ^ n) (hlen : len < 256 ^ n) :
    decodePtrBytesNoForgeProto isRef .slice n
      (encodePtrBytesProto p n ++ encodeLittleEndianBytesProto len n) =
      some (.aggregate [.ptr p n, .scalar len n]) := by
  have hl := encodePtrBytesProto_length p n
  simp only [decodePtrBytesNoForgeProto, decodeWidePtrBytesProto, List.length_append, hl,
    plain_length, Nat.beq_refl, take_append_of_length _ _ n hl, drop_append_of_length _ _ n hl,
    decodeThin_encode isRef _ n hn, normOffset, Nat.mod_eq_of_lt hp, haveFrag_plain,
    dataBytesProto_plain, leValue_leImage, Nat.mod_eq_of_lt hlen]

theorem dataBytesProto_append (l₁ l₂ : List AbstractByteProto) (d₁ d₂ : List UInt8)
    (h₁ : dataBytesProto l₁ = some d₁) (h₂ : dataBytesProto l₂ = some d₂) :
    dataBytesProto (l₁ ++ l₂) = some (d₁ ++ d₂) := by
  induction l₁ generalizing d₁ with
  | nil => simp only [dataBytesProto, Option.some.injEq] at h₁; subst h₁; simpa using h₂
  | cons x rest ih =>
    cases x with
    | uninit => simp [dataBytesProto] at h₁
    | init b fo =>
      cases hr : dataBytesProto rest with
      | none => simp [dataBytesProto, hr] at h₁
      | some ds =>
        simp only [dataBytesProto, hr, Option.some.injEq] at h₁
        subst h₁
        simp only [List.cons_append, dataBytesProto, ih ds hr, List.cons_append]

theorem dataBytesProto_reverse (l : List AbstractByteProto) (d : List UInt8)
    (h : dataBytesProto l = some d) : dataBytesProto l.reverse = some d.reverse := by
  induction l generalizing d with
  | nil => simp only [dataBytesProto, Option.some.injEq] at h; subst h; rfl
  | cons x rest ih =>
    cases x with
    | uninit => simp [dataBytesProto] at h
    | init b fo =>
      cases hr : dataBytesProto rest with
      | none => simp [dataBytesProto, hr] at h
      | some ds =>
        simp only [dataBytesProto, hr, Option.some.injEq] at h
        subst h
        rw [List.reverse_cons, List.reverse_cons]
        exact dataBytesProto_append _ _ _ _ (ih ds hr) rfl

/-- **Reference with stripped provenance is UB, raw pointer degrades to an address
(universal over reversals).** -/
theorem decode_reverse_ref_none_raw_scalar (p : ProvenancePtrProto) (n : Nat) (hn : 2 ≤ n) :
    decodePtrBytesNoForgeProto true .thin n (encodePtrBytesProto p n).reverse = none ∧
    ∃ bits, decodePtrBytesNoForgeProto false .thin n (encodePtrBytesProto p n).reverse =
      some (.scalar bits n) := by
  have hc := coherent_reverse_none p n hn
  have hd := dataBytesProto_encode p.allocId p.tag (normOffset n p.offsetBytes) n
    (normOffset n p.offsetBytes) 0 n
  have hdr : dataBytesProto (encodePtrBytesProto p n).reverse =
      some (leImage (normOffset n p.offsetBytes) n).reverse := by
    simp only [encodePtrBytesProto]
    generalize encodePtrFragsAux p.allocId p.tag (normOffset n p.offsetBytes) n
      (normOffset n p.offsetBytes) 0 n = l at hd
    generalize leImage (normOffset n p.offsetBytes) n = d at hd
    exact dataBytesProto_reverse l d hd
  refine ⟨?_, leValue (leImage (normOffset n p.offsetBytes) n).reverse, ?_⟩ <;>
    simp only [decodePtrBytesNoForgeProto, decodeThinPtrBytesProto, List.length_reverse,
      encodePtrBytesProto_length, Nat.beq_refl, hdr, hc]

/-! ## 6. Option 1 vs Option 2 representation and compatibility projections -/

/-- Option 2 per-byte fragment metadata (provenance pair kept in the legacy `prov` slot). -/
structure PtrByteFragMeta : Type where
  byteIdx : Nat
  origOffset : Nat
  ptrBytes : Nat
deriving DecidableEq

/-- Option 2: legacy `(allocId, tag)` slot plus an optional, defaulted fragment slot. -/
inductive AbstractByteOpt2 : Type where
  | uninit : AbstractByteOpt2
  | init (byte : UInt8) (prov : Option (Nat × Nat)) (frag : Option PtrByteFragMeta := none) :
      AbstractByteOpt2
deriving DecidableEq

/-- Option 2 → Option 1: provenance without fragment metadata fails closed (stripped). -/
def AbstractByteOpt2.toProto : AbstractByteOpt2 → AbstractByteProto
  | .uninit => .uninit
  | .init b (some (a, t)) (some m) => .init b (some ⟨a, t, m.byteIdx, m.origOffset, m.ptrBytes⟩)
  | .init b _ _ => .init b none

def AbstractByteProto.toOpt2 : AbstractByteProto → AbstractByteOpt2
  | .uninit => .uninit
  | .init b none => .init b none none
  | .init b (some f) => .init b (some (f.allocId, f.tag)) (some ⟨f.byteIdx, f.origOffset, f.ptrBytes⟩)

/-- Legacy `(allocId, tag)` projection of an Option 1 byte. -/
def provPair? : AbstractByteProto → Option (Nat × Nat)
  | .init _ (some f) => some (f.allocId, f.tag)
  | _ => none

/-- Plain integer byte (the dominant `.init b .none` call-site shape). -/
def mkInitByte (b : UInt8) : AbstractByteProto := .init b none

/-- Provenance-bearing pointer fragment byte. -/
def mkPtrFragByte (b : UInt8) (allocId tag byteIdx origOffset ptrBytes : Nat) :
    AbstractByteProto :=
  .init b (some ⟨allocId, tag, byteIdx, origOffset, ptrBytes⟩)

/-- Option 2 coherence: decode through the Option 1 projection. -/
def abstractBytesCoherentPtrProvOpt2 (ptrBytes : Nat) (bytes : List AbstractByteOpt2) :
    Option ProvenancePtrProto :=
  abstractBytesCoherentPtrProvProto ptrBytes (bytes.map AbstractByteOpt2.toProto)

theorem toProto_toOpt2 (x : AbstractByteProto) : x.toOpt2.toProto = x := by
  cases x with
  | uninit => rfl
  | init b fo => cases fo <;> rfl

theorem toOpt2_map_toProto (l : List AbstractByteProto) :
    (l.map AbstractByteProto.toOpt2).map AbstractByteOpt2.toProto = l := by
  induction l with
  | nil => rfl
  | cons x rest ih => simp only [List.map_cons, toProto_toOpt2, ih]

/-- Option 1 and Option 2 agree on every byte list (lossless embedding). -/
theorem coherentOpt2_toOpt2 (n : Nat) (l : List AbstractByteProto) :
    abstractBytesCoherentPtrProvOpt2 n (l.map AbstractByteProto.toOpt2) =
      abstractBytesCoherentPtrProvProto n l := by
  simp only [abstractBytesCoherentPtrProvOpt2, toOpt2_map_toProto]

/-- Option 2 plain integer call sites (`.init b .none`) are unchanged by the migration. -/
theorem opt2_plain_toProto (b : UInt8) : (AbstractByteOpt2.init b none).toProto = mkInitByte b :=
  rfl

/-- **Option 2 fails closed (universal):** a provenance-bearing byte without fragment metadata
(an unmigrated `.init b (some (a, t))` call site) strips provenance. -/
theorem coherentOpt2_none_of_missing_frag (n : Nat) (l : List AbstractByteOpt2) (i : Nat)
    (b : UInt8) (pr : Option (Nat × Nat)) (hx : l[i]? = some (.init b pr none)) :
    abstractBytesCoherentPtrProvOpt2 n l = none := by
  apply coherent_none_of_no_frag n _ i b
  rw [List.getElem?_map, hx]
  cases pr with
  | none => rfl
  | some q => cases q; rfl

theorem provPair_mkPtrFragByte (b : UInt8) (a t i o n : Nat) :
    provPair? (mkPtrFragByte b a t i o n) = some (a, t) := rfl

/-- A legacy two-argument pattern written against Option 2 (as every existing
`| .init _ (.some _) => …` arm would read after the migration). -/
def opt2LegacyHasProv : AbstractByteOpt2 → Bool
  | .init _ (some _) => true
  | _ => false

/-- **Option 2 migration hazard (kernel-checked):** Lean elaborates the two-argument pattern
`.init _ (some _)` as `.init _ (some _) none` (the defaulted field is filled in the pattern),
so it silently stops matching fragment-carrying bytes and falls through to the catch-all arm.
Every one of the census' 2-argument `AbstractByte.init` patterns would change meaning. -/
theorem opt2_legacy_pattern_hazard :
    opt2LegacyHasProv (.init 0 (some (1, 1))) = true ∧
    opt2LegacyHasProv (.init 0 (some (1, 1)) (some ⟨0, 0, 8⟩)) = false := ⟨rfl, rfl⟩

/-! ## 7. Faithful mirror of Miri's `PointerFrag` / `inspectFragments` -/

/-- Verbatim mirror of `lean-miri/vendor/Miri/Memory/ProvenanceMap.lean:17-21`
(`rust#148259`, CTFE per-byte pointer fragments):
```
structure PointerFrag (Prov : Type u) where
  idx : UInt8
  prov : Prov
  bytes : Vector UInt8 8
```
-/
structure PointerFragMirror (Prov : Type) : Type where
  idx : UInt8
  prov : Prov
  bytes : Vector UInt8 8
deriving DecidableEq

/-- Outcome of `inspectFragments` (only the `missingWildcard` error is reachable once the
per-position `getByte` lookups have succeeded). -/
inductive InspectOutcome (Prov : Type) : Type where
  | ok (prov : Option Prov) : InspectOutcome Prov
  | missingWildcard : InspectOutcome Prov
deriving DecidableEq

/-- Loop body of `inspectFragments`
(`lean-miri/vendor/Miri/Memory/ProvenanceMap.lean:117-139`), with the per-position fragment
lookups `self.getByte (offset + idx)` supplied as the list `fragments`:
```
  let mut expected : Option (Prov × Vector UInt8 8) := none
  for idx in [:pointerSize.bytes.toNat] do
    ...
    let some frag := fragment | return none
    if some frag.prov == PointerProvenance.wildcard (Prov := Prov) then continue
    if frag.idx.toNat != idx then return none
    match expected with
    | some pair =>
        if (frag.prov, frag.bytes) != pair then return none
    | none => expected := some (frag.prov, frag.bytes)
  match expected with
  | some (prov, _) => return some prov
  | none =>
      match PointerProvenance.wildcard (Prov := Prov) with
      | some wildcard => return some wildcard
      | none => throw .missingWildcard
```
-/
def inspectFragmentsMirrorLoop {Prov : Type} [DecidableEq Prov] (wildcard : Option Prov) :
    Nat → Option (Prov × Vector UInt8 8) → List (Option (PointerFragMirror Prov)) →
      InspectOutcome Prov
  | _, expected, [] =>
    match expected with
    | some (prov, _) => .ok (some prov)
    | none =>
      match wildcard with
      | some w => .ok (some w)
      | none => .missingWildcard
  | idx, expected, fragment :: rest =>
    match fragment with
    | none => .ok none
    | some frag =>
      if some frag.prov == wildcard then
        inspectFragmentsMirrorLoop wildcard (idx + 1) expected rest
      else if frag.idx.toNat != idx then .ok none
      else
        match expected with
        | some pair =>
          if (frag.prov, frag.bytes) != pair then .ok none
          else inspectFragmentsMirrorLoop wildcard (idx + 1) expected rest
        | none => inspectFragmentsMirrorLoop wildcard (idx + 1) (some (frag.prov, frag.bytes)) rest

def inspectFragmentsMirror {Prov : Type} [DecidableEq Prov] (wildcard : Option Prov)
    (fragments : List (Option (PointerFragMirror Prov))) : InspectOutcome Prov :=
  inspectFragmentsMirrorLoop wildcard 0 none fragments

/-- Miri's `PointerFrag.bytes`: the originating pointer's full 8-byte little-endian image. -/
def imageVec8 (off : Nat) : Vector UInt8 8 :=
  ⟨(leImage off 8).toArray, by simp [leImage_length]⟩

/-- Project a prototype byte to its Miri provenance-map fragment (CTFE provenance
`(allocId, tag)`, no wildcard). -/
def toMiriFrag : AbstractByteProto → Option (PointerFragMirror (Nat × Nat))
  | .init _ (some f) => some ⟨UInt8.ofNat f.byteIdx, (f.allocId, f.tag), imageVec8 f.origOffset⟩
  | _ => none

theorem imageVec8_inj (o₁ o₂ : Nat) (h : imageVec8 o₁ = imageVec8 o₂) :
    o₁ % 256 ^ 8 = o₂ % 256 ^ 8 := by
  have hl : leImage o₁ 8 = leImage o₂ 8 := by
    have := congrArg Vector.toArray h
    exact List.toArray_inj this
  rw [← leValue_leImage, ← leValue_leImage, hl]

theorem uint8_ofNat_toNat_of_lt (i : Nat) (h : i < 256) : (UInt8.ofNat i).toNat = i := by
  rw [show (UInt8.ofNat i).toNat = i % 256 from UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem miri_loop_of_frags (a t o n : Nat) :
    ∀ (l : List AbstractByteProto) (idx : Nat),
      (∀ (i : Nat) (x : AbstractByteProto), l[i]? = some x →
        ∃ b, x = .init b (some ⟨a, t, idx + i, o, n⟩)) →
      idx + l.length ≤ 256 →
      inspectFragmentsMirrorLoop none idx (some ((a, t), imageVec8 o)) (l.map toMiriFrag) =
        .ok (some (a, t)) := by
  intro l
  induction l with
  | nil => intro _ _ _; rfl
  | cons x rest ih =>
    intro idx hall hlen
    obtain ⟨b, rfl⟩ := hall 0 x rfl
    have hidx : idx < 256 := by
      simp only [List.length_cons] at hlen
      exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos _)) hlen
    have hrest : ∀ (i : Nat) (y : AbstractByteProto), rest[i]? = some y →
        ∃ b, y = .init b (some ⟨a, t, idx + 1 + i, o, n⟩) := by
      intro i y hy
      obtain ⟨b', hb'⟩ := hall (i + 1) y (by simpa using hy)
      exact ⟨b', by rw [hb', Nat.add_assoc, Nat.add_comm 1 i]⟩
    have hlen' : idx + 1 + rest.length ≤ 256 := by
      simp only [List.length_cons] at hlen
      rw [Nat.add_assoc, Nat.add_comm 1]
      exact hlen
    simp only [List.map_cons, toMiriFrag, inspectFragmentsMirrorLoop, Nat.add_zero,
      uint8_ofNat_toNat_of_lt idx hidx]
    simp [ih (idx + 1) hrest hlen']

/-- **Proto ⇒ Miri (universal, `ptrBytes ≤ 8`):** whenever the prototype keeps provenance,
Miri's `inspectFragments` recovers the same `(allocId, tag)`. -/
theorem miri_of_coherent (n : Nat) (hn8 : n ≤ 8) (l : List AbstractByteProto)
    (p : ProvenancePtrProto) (h : abstractBytesCoherentPtrProvProto n l = some p) :
    inspectFragmentsMirror none (l.map toMiriFrag) = .ok (some (p.allocId, p.tag)) := by
  obtain ⟨hlen, hall⟩ := coherent_some_frags n l p h
  cases l with
  | nil => simp [abstractBytesCoherentPtrProvProto] at h
  | cons x rest =>
    obtain ⟨b, rfl⟩ := hall 0 x rfl
    have hrest : ∀ (i : Nat) (y : AbstractByteProto), rest[i]? = some y →
        ∃ b, y = .init b (some ⟨p.allocId, p.tag, 1 + i, p.offsetBytes, n⟩) := by
      intro i y hy
      obtain ⟨b', hb'⟩ := hall (i + 1) y (by simpa using hy)
      exact ⟨b', by rw [hb', Nat.add_comm 1 i]⟩
    have hlen' : 1 + rest.length ≤ 256 := by
      simp only [List.length_cons] at hlen
      rw [Nat.add_comm, hlen]
      exact Nat.le_trans hn8 (by decide)
    simp only [inspectFragmentsMirror, List.map_cons, toMiriFrag, inspectFragmentsMirrorLoop]
    simp [miri_loop_of_frags _ _ _ _ rest 1 hrest hlen']

/-- Well-formedness of a fragment-carrying byte list at target pointer width `n` (the Miri
allocation invariants): one target width, in-range fragment index and normalized offset, and
data bytes equal to the originating image byte (writes of data clear fragments). -/
def FragsWellFormed (n : Nat) (l : List AbstractByteProto) : Prop :=
  ∀ (i : Nat) (b : UInt8) (f : PtrByteFragProto), l[i]? = some (.init b (some f)) →
    f.ptrBytes = n ∧ f.byteIdx < 256 ∧ f.origOffset < 256 ^ n ∧
      b = UInt8.ofNat (f.origOffset / 256 ^ f.byteIdx)

/-- Intact prototype pointer images satisfy the Miri allocation invariants. -/
theorem fragsWellFormed_encode (p : ProvenancePtrProto) (n : Nat) (hn : n ≤ 256) :
    FragsWellFormed n (encodePtrBytesProto p n) := by
  intro i b f hx
  have hi : i < n := by
    have := (List.getElem?_eq_some_iff.1 hx).1
    rwa [encodePtrBytesProto_length] at this
  rw [encodePtrBytesProto_getElem? p n i hi] at hx
  simp only [Option.some.injEq, AbstractByteProto.init.injEq] at hx
  obtain ⟨rfl, rfl⟩ := hx
  exact ⟨rfl, Nat.lt_of_lt_of_le hi hn, Nat.mod_lt _ (Nat.pow_pos (by decide)), rfl⟩

theorem miri_loop_inv (a t : Nat) (v : Vector UInt8 8) :
    ∀ (l : List AbstractByteProto) (idx : Nat) (q : Nat × Nat),
      inspectFragmentsMirrorLoop none idx (some ((a, t), v)) (l.map toMiriFrag) = .ok (some q) →
      q = (a, t) ∧
      ∀ (i : Nat) (x : AbstractByteProto), l[i]? = some x →
        ∃ b f, x = .init b (some f) ∧ (UInt8.ofNat f.byteIdx).toNat = idx + i ∧
          f.allocId = a ∧ f.tag = t ∧ imageVec8 f.origOffset = v := by
  intro l
  induction l with
  | nil =>
    intro idx q h
    simp only [List.map_nil, inspectFragmentsMirrorLoop, InspectOutcome.ok.injEq,
      Option.some.injEq] at h
    exact ⟨h.symm, fun i x hx => by simp at hx⟩
  | cons x rest ih =>
    intro idx q h
    cases x with
    | uninit => simp [toMiriFrag, inspectFragmentsMirrorLoop] at h
    | init b fo =>
      cases fo with
      | none => simp [toMiriFrag, inspectFragmentsMirrorLoop] at h
      | some f =>
        simp only [List.map_cons, toMiriFrag, inspectFragmentsMirrorLoop] at h
        simp only [reduceCtorEq, beq_iff_eq, ite_false, bne_iff_ne, ne_eq,
          ite_not, Prod.mk.injEq] at h
        split at h
        · rename_i hid
          split at h
          · rename_i hpair
            obtain ⟨⟨ha, ht⟩, hv⟩ := hpair
            obtain ⟨hq, hall⟩ := ih (idx + 1) q h
            refine ⟨hq, ?_⟩
            intro i y hy
            cases i with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
              subst hy
              exact ⟨b, f, rfl, by rw [hid, Nat.add_zero], ha, ht, hv⟩
            | succ i =>
              simp only [List.getElem?_cons_succ] at hy
              obtain ⟨b', f', hy', hidx, h1, h2, h3⟩ := hall i y hy
              exact ⟨b', f', hy', by rw [hidx, Nat.add_assoc, Nat.add_comm 1 i], h1, h2, h3⟩
          · simp at h
        · simp at h

/-- **Miri ⇒ Proto (universal, well-formed fragments, `0 < ptrBytes ≤ 8`):** whenever Miri's
`inspectFragments` recovers provenance (no wildcard), the bytes are exactly an intact
prototype pointer image, which the prototype decodes with the same `(allocId, tag)`. -/
theorem coherent_of_miri (n : Nat) (hn : 0 < n) (hn8 : n ≤ 8) (l : List AbstractByteProto)
    (hlen : l.length = n) (hwf : FragsWellFormed n l) (q : Nat × Nat)
    (h : inspectFragmentsMirror none (l.map toMiriFrag) = .ok (some q)) :
    ∃ o, o < 256 ^ n ∧ l = encodePtrBytesProto ⟨q.1, q.2, o⟩ n ∧
      abstractBytesCoherentPtrProvProto n l = some ⟨q.1, q.2, o⟩ := by
  cases l with
  | nil => simp at hlen; subst hlen; exact absurd hn (Nat.lt_irrefl 0)
  | cons x rest =>
    cases x with
    | uninit => simp [inspectFragmentsMirror, toMiriFrag, inspectFragmentsMirrorLoop] at h
    | init b0 fo =>
      cases fo with
      | none => simp [inspectFragmentsMirror, toMiriFrag, inspectFragmentsMirrorLoop] at h
      | some f0 =>
        obtain ⟨hp0, hi0, ho0, hb0⟩ := hwf 0 b0 f0 rfl
        have hidx0 : f0.byteIdx = 0 := by
          have hh := h
          simp only [inspectFragmentsMirror, List.map_cons, toMiriFrag,
            inspectFragmentsMirrorLoop] at hh
          simp only [reduceCtorEq, beq_iff_eq, ite_false, bne_iff_ne, ne_eq, ite_not] at hh
          split at hh
          · rename_i hid
            rw [uint8_ofNat_toNat_of_lt _ hi0] at hid
            exact hid
          · simp at hh
        have hloop : inspectFragmentsMirrorLoop none 0 none (List.map toMiriFrag
            (.init b0 (some f0) :: rest)) = .ok (some q) := h
        simp only [List.map_cons, toMiriFrag, inspectFragmentsMirrorLoop] at hloop
        simp only [reduceCtorEq, beq_iff_eq, ite_false, bne_iff_ne, ne_eq, ite_not,
          hidx0] at hloop
        obtain ⟨hq, hall⟩ := miri_loop_inv f0.allocId f0.tag (imageVec8 f0.origOffset) rest 1 q
          hloop
        subst hq
        have hl : (List.cons (AbstractByteProto.init b0 (some f0)) rest) =
            encodePtrBytesProto ⟨f0.allocId, f0.tag, f0.origOffset⟩ n := by
          apply List.ext_getElem?
          intro i
          have hnorm : normOffset n f0.origOffset = f0.origOffset := Nat.mod_eq_of_lt ho0
          cases i with
          | zero =>
            rw [encodePtrBytesProto_getElem? _ n 0 hn]
            simp only [List.getElem?_cons_zero, hnorm, Nat.pow_zero, Nat.div_one]
            rw [hb0, hidx0, Nat.pow_zero, Nat.div_one, ← hp0, ← hidx0]
          | succ i =>
            simp only [List.getElem?_cons_succ]
            cases hy : rest[i]? with
            | none =>
              have hge : rest.length ≤ i := by
                rw [List.getElem?_eq_none_iff] at hy; exact hy
              rw [List.getElem?_eq_none]
              rw [encodePtrBytesProto_length, ← hlen]
              simp only [List.length_cons]
              exact Nat.succ_le_succ hge
            | some y =>
              have hlt : i + 1 < n := by
                rw [← hlen]
                simp only [List.length_cons]
                exact Nat.succ_lt_succ ((List.getElem?_eq_some_iff.1 hy).1)
              obtain ⟨b, f, rfl, hidx, ha, ht, hv⟩ := hall i _ hy
              obtain ⟨hp, hib, hob, hbb⟩ := hwf (i + 1) b f (by simpa using hy)
              rw [uint8_ofNat_toNat_of_lt _ hib, Nat.add_comm 1 i] at hidx
              have ho : f.origOffset = f0.origOffset := by
                have h8 := imageVec8_inj _ _ hv
                have hle : 256 ^ n ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hn8
                rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hob hle),
                  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ho0 hle)] at h8
                exact h8
              rw [encodePtrBytesProto_getElem? _ n (i + 1) hlt, hnorm, hbb, hidx, ho]
              cases f
              simp only at ha ht hidx ho hp ⊢
              subst ha ht hidx ho hp
              rfl
        refine ⟨f0.origOffset, ho0, hl, ?_⟩
        rw [hl, coherent_encode _ n hn]
        simp only [normOffset, Nat.mod_eq_of_lt ho0]

/-! ## 8. Bridge to live `MiniRustSpec.Interp` (`decode_ptr` / `encode_ptr`) -/

/-- Project a prototype byte to a MiniRust `AbstractByte<Provenance<()>>`: MiniRust's
`BasicMemory` provenance is the `AllocId` only (no Tree Borrows tag) and its
`ProvenanceFrag { provenance, position }` keeps the byte position but no pointer image. -/
def AbstractByteProto.toMiniRust : AbstractByteProto → MiniRustSpec.Interp.Byte
  | .uninit => .Uninit
  | .init b none => .Init b none
  | .init b (some f) =>
    .Init b (some { provenance := (⟨(f.allocId : Int)⟩, ()), position := (f.byteIdx : Int) })

/-- MiniRust provenance carried by allocation `a`. -/
def mrProv (a : Nat) : MiniRustSpec.Interp.Prov := (⟨(a : Int)⟩, ())

/-- The provenance computed by live `MiniRustSpec.Interp.decodePtr` on `bytes`. -/
def mrDecodedProv (bytes : List MiniRustSpec.Interp.Byte) : Option MiniRustSpec.Interp.Prov :=
  MiniRustSpec.Interp.decodePtrProvenance 0 (MiniRustSpec.Interp.firstProvenance bytes) bytes

/-- **Proto encoding = live MiniRust `encode_ptr` bytes (universal, modulo tag erasure).** -/
theorem toMiniRust_encodeAux (a t o n bits idx k : Nat) :
    (encodePtrFragsAux a t o n bits idx k).map AbstractByteProto.toMiniRust =
      MiniRustSpec.Interp.encodePtrBytes (some (mrProv a)) idx (leImage bits k) := by
  induction k generalizing bits idx with
  | zero => rfl
  | succ k ih =>
    simp only [encodePtrFragsAux, leImage, List.map_cons, ih,
      MiniRustSpec.Interp.encodePtrBytes, AbstractByteProto.toMiniRust, mrProv, Option.map_some]

theorem toMiniRust_encode (p : ProvenancePtrProto) (n : Nat) :
    (encodePtrBytesProto p n).map AbstractByteProto.toMiniRust =
      MiniRustSpec.Interp.encodePtrBytes (some (mrProv p.allocId)) 0
        (leImage (normOffset n p.offsetBytes) n) :=
  toMiniRust_encodeAux _ _ _ _ _ _ _

theorem mr_keep (a : Nat) :
    ∀ (l : List AbstractByteProto) (idx : Nat),
      (∀ (i : Nat) (x : AbstractByteProto), l[i]? = some x →
        ∃ b f, x = .init b (some f) ∧ f.allocId = a ∧ f.byteIdx = idx + i) →
      MiniRustSpec.Interp.decodePtrProvenance idx (some (mrProv a))
        (l.map AbstractByteProto.toMiniRust) = some (mrProv a) := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons x rest ih =>
    intro idx hall
    obtain ⟨b, f, rfl, ha, hi⟩ := hall 0 x rfl
    have hrest : ∀ (i : Nat) (y : AbstractByteProto), rest[i]? = some y →
        ∃ b f, y = .init b (some f) ∧ f.allocId = a ∧ f.byteIdx = idx + 1 + i := by
      intro i y hy
      obtain ⟨b', f', hy', ha', hi'⟩ := hall (i + 1) y (by simpa using hy)
      exact ⟨b', f', hy', ha', by rw [hi', Nat.add_assoc, Nat.add_comm 1 i]⟩
    simp only [List.map_cons, MiniRustSpec.Interp.decodePtrProvenance,
      AbstractByteProto.toMiniRust, MiniRustSpec.Interp.AbstractByte.provenance_frag, ha, hi,
      Nat.add_zero, mrProv, and_self, ite_pos']
    exact ih (idx + 1) hrest

/-- **Proto refines MiniRust (universal):** whenever the prototype keeps provenance, live
MiniRust `decode_ptr` keeps the same allocation. -/
theorem mr_of_coherent (n : Nat) (l : List AbstractByteProto) (p : ProvenancePtrProto)
    (h : abstractBytesCoherentPtrProvProto n l = some p) :
    mrDecodedProv (l.map AbstractByteProto.toMiniRust) = some (mrProv p.allocId) := by
  obtain ⟨_, hall⟩ := coherent_some_frags n l p h
  cases l with
  | nil => simp [abstractBytesCoherentPtrProvProto] at h
  | cons x rest =>
    obtain ⟨b, rfl⟩ := hall 0 x rfl
    have hall' : ∀ (i : Nat) (y : AbstractByteProto), (AbstractByteProto.init b
        (some ⟨p.allocId, p.tag, 0, p.offsetBytes, n⟩) :: rest)[i]? = some y →
        ∃ b f, y = .init b (some f) ∧ f.allocId = p.allocId ∧ f.byteIdx = 0 + i := by
      intro i y hy
      obtain ⟨b', hb'⟩ := hall i y hy
      exact ⟨b', _, hb', rfl, (Nat.zero_add i).symm⟩
    have hfirst : MiniRustSpec.Interp.firstProvenance
        ((AbstractByteProto.init b (some ⟨p.allocId, p.tag, 0, p.offsetBytes, n⟩) :: rest).map
          AbstractByteProto.toMiniRust) = some (mrProv p.allocId) := rfl
    simp only [mrDecodedProv, hfirst]
    exact mr_keep p.allocId _ 0 hall'

theorem mr_none_acc :
    ∀ (l : List MiniRustSpec.Interp.Byte) (idx : Nat),
      MiniRustSpec.Interp.decodePtrProvenance idx none l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons y rest ih =>
    intro idx
    simp only [MiniRustSpec.Interp.decodePtrProvenance]
    split
    · simp [ih]
    · exact ih (idx + 1)

theorem mr_strip (q : MiniRustSpec.Interp.Prov) :
    ∀ (l : List AbstractByteProto) (idx : Nat) (acc : Option MiniRustSpec.Interp.Prov)
      (j : Nat) (x : AbstractByteProto),
      (acc = some q ∨ acc = none) → l[j]? = some x →
      (∀ fr, MiniRustSpec.Interp.AbstractByte.provenance_frag x.toMiniRust = some fr →
        fr.position ≠ ((idx + j : Nat) : Int) ∨ fr.provenance ≠ q) →
      MiniRustSpec.Interp.decodePtrProvenance idx acc (l.map AbstractByteProto.toMiniRust) =
        none := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _ hx; simp at hx
  | cons y rest ih =>
    intro idx acc j x hacc hx hbad
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      simp only [List.map_cons, MiniRustSpec.Interp.decodePtrProvenance]
      split
      · rename_i fr hfr
        have hb := hbad fr hfr
        rw [ite_neg']
        · exact mr_none_acc _ _
        · intro hc
          rcases hacc with rfl | rfl
          · rcases hb with hb | hb
            · exact hb (by simpa using hc.1)
            · exact hb (by simpa using hc.2)
          · simp at hc
      · exact mr_none_acc _ _
    | succ j =>
      simp only [List.getElem?_cons_succ] at hx
      simp only [List.map_cons, MiniRustSpec.Interp.decodePtrProvenance]
      have hbad' : ∀ fr, MiniRustSpec.Interp.AbstractByte.provenance_frag x.toMiniRust =
          some fr → fr.position ≠ ((idx + 1 + j : Nat) : Int) ∨ fr.provenance ≠ q := by
        intro fr hfr
        rw [Nat.add_assoc, Nat.add_comm 1 j]
        exact hbad fr hfr
      split
      · split
        · exact ih (idx + 1) acc j x hacc hx hbad'
        · exact ih (idx + 1) none j x (Or.inr rfl) hx hbad'
      · exact ih (idx + 1) none j x (Or.inr rfl) hx hbad'

theorem mr_strip_top (l : List AbstractByteProto) (j : Nat) (x : AbstractByteProto)
    (hx : l[j]? = some x)
    (hbad : ∀ q fr, MiniRustSpec.Interp.AbstractByte.provenance_frag x.toMiniRust = some fr →
      fr.position ≠ (j : Int) ∨ fr.provenance ≠ q) :
    mrDecodedProv (l.map AbstractByteProto.toMiniRust) = none := by
  unfold mrDecodedProv
  cases hf : MiniRustSpec.Interp.firstProvenance (l.map AbstractByteProto.toMiniRust) with
  | none =>
    exact mr_strip (mrProv 0) l 0 none j x (Or.inr rfl) hx
      (fun fr hfr => by rw [Nat.zero_add]; exact hbad _ fr hfr)
  | some q =>
    exact mr_strip q l 0 (some q) j x (Or.inl rfl) hx
      (fun fr hfr => by rw [Nat.zero_add]; exact hbad q fr hfr)

/-- **3-way agreement on misplaced bytes (universal):** a byte whose fragment index differs from
its position is stripped by the prototype AND by live MiniRust (and by Miri, whose
`frag.idx.toNat != idx` check fires). -/
theorem agree_strip_moved (n : Nat) (l : List AbstractByteProto) (i : Nat) (b : UInt8)
    (f : PtrByteFragProto) (hx : l[i]? = some (.init b (some f))) (hne : f.byteIdx ≠ i) :
    abstractBytesCoherentPtrProvProto n l = none ∧
      mrDecodedProv (l.map AbstractByteProto.toMiniRust) = none := by
  refine ⟨coherent_none_of_byteIdx_ne n l i b f hx hne, mr_strip_top l i _ hx ?_⟩
  intro q fr hfr
  left
  simp only [AbstractByteProto.toMiniRust, MiniRustSpec.Interp.AbstractByte.provenance_frag,
    Option.some.injEq] at hfr
  subst hfr
  intro h
  exact hne (Int.ofNat_inj.mp h)

/-- **3-way agreement on missing provenance (universal):** a plain integer byte anywhere. -/
theorem agree_strip_plain (n : Nat) (l : List AbstractByteProto) (i : Nat) (b : UInt8)
    (hx : l[i]? = some (.init b none)) :
    abstractBytesCoherentPtrProvProto n l = none ∧
      mrDecodedProv (l.map AbstractByteProto.toMiniRust) = none :=
  ⟨coherent_none_of_no_frag n l i b hx,
    mr_strip_top l i _ hx (fun _ fr hfr => by simp [AbstractByteProto.toMiniRust,
      MiniRustSpec.Interp.AbstractByte.provenance_frag] at hfr)⟩

/-- **3-way agreement on mixed allocations (universal):** two fragments of different
allocations anywhere in the image. -/
theorem agree_strip_mixed_alloc (n : Nat) (l : List AbstractByteProto) (i j : Nat) (b b' : UInt8)
    (f g : PtrByteFragProto) (hi : l[i]? = some (.init b (some f)))
    (hj : l[j]? = some (.init b' (some g))) (hne : f.allocId ≠ g.allocId) :
    abstractBytesCoherentPtrProvProto n l = none ∧
      mrDecodedProv (l.map AbstractByteProto.toMiniRust) = none := by
  refine ⟨coherent_none_of_frag_mismatch n l i j b b' f g hi hj
    (fun h => hne (congrArg Prod.fst h)), ?_⟩
  unfold mrDecodedProv
  cases hf : MiniRustSpec.Interp.firstProvenance (l.map AbstractByteProto.toMiniRust) with
  | none =>
    exact mr_strip (mrProv (f.allocId + 1)) l 0 none i _ (Or.inr rfl) hi (fun fr hfr => by
      simp only [AbstractByteProto.toMiniRust, MiniRustSpec.Interp.AbstractByte.provenance_frag,
        Option.some.injEq] at hfr
      subst hfr
      right
      intro h
      simp only [mrProv, Prod.mk.injEq, MiniRustSpec.Gen.AllocId.mk.injEq, and_true] at h
      exact Int.ne_of_lt (Int.lt_succ _) (h.trans (by simp)))
  | some q =>
    cases decEq q (mrProv f.allocId) with
    | isTrue hq =>
      exact mr_strip q l 0 (some q) j _ (Or.inl rfl) hj (fun fr hfr => by
        right
        simp only [AbstractByteProto.toMiniRust, MiniRustSpec.Interp.AbstractByte.provenance_frag,
          Option.some.injEq] at hfr
        subst hfr hq
        simp only [mrProv, ne_eq, Prod.mk.injEq, MiniRustSpec.Gen.AllocId.mk.injEq,
          Int.natCast_inj, and_true]
        exact fun h => hne h.symm)
    | isFalse hq =>
      exact mr_strip q l 0 (some q) i _ (Or.inl rfl) hi (fun fr hfr => by
        right
        simp only [AbstractByteProto.toMiniRust, MiniRustSpec.Interp.AbstractByte.provenance_frag,
          Option.some.injEq] at hfr
        subst hfr
        exact fun h => hq h.symm)

theorem spliceBytes_getElem? {α : Type} (k : Nat) (l₁ l₂ : List α) (hk : k ≤ l₁.length)
    (i : Nat) : (spliceBytes k l₁ l₂)[i]? = if i < k then l₁[i]? else l₂[i]? := by
  have hlt : (l₁.take k).length = k := by simp [Nat.min_eq_left hk]
  rcases Nat.lt_or_ge i k with h | h
  · rw [ite_pos' h, spliceBytes, List.getElem?_append_left (by rw [hlt]; exact h),
      List.getElem?_take, ite_pos' h]
  · rw [ite_neg' (Nat.not_lt_of_ge h), spliceBytes, List.getElem?_append_right (by rw [hlt]; exact h),
      hlt, List.getElem?_drop, Nat.add_sub_cancel' h]

/-- **Strict refinement over vendored MiniRust (universal, `UCG#558`):** splicing two
same-allocation pointers keeps provenance in live MiniRust `decode_ptr` (which tracks only the
byte position), whereas the prototype strips it whenever the offsets (or tags) differ. -/
theorem mr_keeps_same_alloc_splice (p₁ p₂ : ProvenancePtrProto) (n k : Nat) (hk0 : 0 < k)
    (hkn : k < n) (ha : p₁.allocId = p₂.allocId) :
    mrDecodedProv ((spliceBytes k (encodePtrBytesProto p₁ n) (encodePtrBytesProto p₂ n)).map
      AbstractByteProto.toMiniRust) = some (mrProv p₁.allocId) := by
  have hl₁ := encodePtrBytesProto_length p₁ n
  have hall : ∀ (i : Nat) (x : AbstractByteProto),
      (spliceBytes k (encodePtrBytesProto p₁ n) (encodePtrBytesProto p₂ n))[i]? = some x →
      ∃ b f, x = .init b (some f) ∧ f.allocId = p₁.allocId ∧ f.byteIdx = 0 + i := by
    intro i x hx
    rw [spliceBytes_getElem? k _ _ (by rw [hl₁]; exact Nat.le_of_lt hkn)] at hx
    rcases Nat.lt_or_ge i k with h | h
    · rw [ite_pos' h, encodePtrBytesProto_getElem? _ n i (Nat.lt_trans h hkn)] at hx
      exact ⟨_, _, (Option.some.inj hx).symm, rfl, (Nat.zero_add i).symm⟩
    · rw [ite_neg' (Nat.not_lt_of_ge h)] at hx
      rcases Nat.lt_or_ge i n with h' | h'
      · rw [encodePtrBytesProto_getElem? _ n i h'] at hx
        exact ⟨_, _, (Option.some.inj hx).symm, ha.symm, (Nat.zero_add i).symm⟩
      · rw [List.getElem?_eq_none (by rw [encodePtrBytesProto_length]; exact h')] at hx
        simp at hx
  have h0 := hall 0
  have hx0 : (spliceBytes k (encodePtrBytesProto p₁ n) (encodePtrBytesProto p₂ n))[0]? =
      (encodePtrBytesProto p₁ n)[0]? := by
    rw [spliceBytes_getElem? k _ _ (by rw [hl₁]; exact Nat.le_of_lt hkn), ite_pos' hk0]
  rw [encodePtrBytesProto_getElem? _ n 0 (Nat.lt_trans hk0 hkn)] at hx0
  generalize hL : spliceBytes k (encodePtrBytesProto p₁ n) (encodePtrBytesProto p₂ n) = L at hall hx0
  cases L with
  | nil => simp at hx0
  | cons y rest =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx0
    subst hx0
    have hfirst : MiniRustSpec.Interp.firstProvenance ((AbstractByteProto.init
        (UInt8.ofNat (normOffset n p₁.offsetBytes / 256 ^ 0))
        (some ⟨p₁.allocId, p₁.tag, 0, normOffset n p₁.offsetBytes, n⟩) :: rest).map
          AbstractByteProto.toMiniRust) = some (mrProv p₁.allocId) := rfl
    simp only [mrDecodedProv, hfirst]
    exact mr_keep p₁.allocId _ 0 hall

/-! ## 9. In-order byte copy and read-time untyped-byte validity (`Kani#5205` / `#5196`) -/

/-- Untyped byte-buffer write (`ptr::write` of raw bytes / `write_bytes` payload): fails only
when out of bounds, never on the byte values. -/
def writeBytesProto (buf : List AbstractByteProto) (off : Nat) (patch : List AbstractByteProto) :
    Option (List AbstractByteProto) :=
  match Nat.ble (off + patch.length) buf.length with
  | true => some (buf.take off ++ patch ++ buf.drop (off + patch.length))
  | false => none

/-- Untyped byte-buffer read of `len` bytes at `off`. -/
def readBytesProto (buf : List AbstractByteProto) (off len : Nat) :
    Option (List AbstractByteProto) :=
  match Nat.ble (off + len) buf.length with
  | true => some ((buf.drop off).take len)
  | false => none

/-- Untyped `copy_nonoverlapping(src + srcOff, dst + dstOff, len)` over byte buffers. -/
def copyNonOverlappingBytesProto (src dst : List AbstractByteProto) (srcOff dstOff len : Nat) :
    Option (List AbstractByteProto) :=
  match readBytesProto src srcOff len with
  | some bs => writeBytesProto dst dstOff bs
  | none => none

/-- `write_bytes(dst + off, val, count)` over a byte buffer. -/
def writeBytesFillProto (buf : List AbstractByteProto) (off : Nat) (val : UInt8) (count : Nat) :
    Option (List AbstractByteProto) :=
  writeBytesProto buf off (List.replicate count (mkInitByte val))

/-- In-order byte-by-byte copy (`for i in 0..n { *dst.add(i) = *src.add(i) }` through `u8`
places / `MaybeUninit<u8>`), overwriting the destination prefix. -/
def copyBytewiseProto : List AbstractByteProto → List AbstractByteProto → List AbstractByteProto
  | s :: ss, _ :: ds => s :: copyBytewiseProto ss ds
  | [], ds => ds
  | _ :: _, [] => []

/-- Typed read of `ty` at byte offset `off` of an untyped buffer. -/
def readTypedFromBytesProto (ptrBytes : Nat) (ty : TyProto) (buf : List AbstractByteProto)
    (off : Nat) : Option ValueProto :=
  match readBytesProto buf off (ty.sizeBytes ptrBytes) with
  | some bs => decodeTypedValueFromBytesProto ptrBytes ty bs
  | none => none

theorem copyBytewise_eq (src dst : List AbstractByteProto) (h : dst.length = src.length) :
    copyBytewiseProto src dst = src := by
  induction src generalizing dst with
  | nil => cases dst with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x rest ih =>
    cases dst with
    | nil => simp at h
    | cons y ds => simp only [copyBytewiseProto, ih ds (by simpa using h)]

/-- **In-order byte-by-byte copy preserves fragments and provenance (universal).** -/
theorem copyBytewise_preserves_ptr (isRef : Bool) (p : ProvenancePtrProto) (n : Nat) (hn : 0 < n)
    (hoff : p.offsetBytes < 256 ^ n) (dst : List AbstractByteProto) (hd : dst.length = n) :
    copyBytewiseProto (encodePtrBytesProto p n) dst = encodePtrBytesProto p n ∧
    decodePtrBytesNoForgeProto isRef .thin n (copyBytewiseProto (encodePtrBytesProto p n) dst) =
      some (.ptr p n) := by
  have hc := copyBytewise_eq (encodePtrBytesProto p n) dst
    (by rw [hd, encodePtrBytesProto_length])
  exact ⟨hc, by rw [hc]; exact decode_encode_thin_exact isRef p n hn hoff⟩

/-- **Bulk `copy_nonoverlapping` of a whole pointer image preserves provenance (universal).** -/
theorem copyNonOverlapping_preserves_ptr (isRef : Bool) (p : ProvenancePtrProto) (n : Nat)
    (hn : 0 < n) (hoff : p.offsetBytes < 256 ^ n) (dst : List AbstractByteProto)
    (hd : dst.length = n) :
    copyNonOverlappingBytesProto (encodePtrBytesProto p n) dst 0 0 n =
      some (encodePtrBytesProto p n) ∧
    decodePtrBytesNoForgeProto isRef .thin n (encodePtrBytesProto p n) = some (.ptr p n) := by
  have hl := encodePtrBytesProto_length p n
  refine ⟨?_, decode_encode_thin_exact isRef p n hn hoff⟩
  have h1 : List.take n (encodePtrBytesProto p n) = encodePtrBytesProto p n :=
    List.take_of_length_le (Nat.le_of_eq hl)
  simp only [copyNonOverlappingBytesProto, readBytesProto, writeBytesProto, Nat.zero_add,
    List.drop_zero, List.take_zero, List.nil_append, Nat.ble_eq_true_of_le (Nat.le_refl n), h1, hl,
    List.drop_eq_nil_of_le (Nat.le_of_eq hd), List.append_nil, hd]

/-- **Untyped writes never fault on byte values (universal):** any in-bounds patch succeeds,
including invalid `bool` / `char` bit patterns. -/
theorem writeBytesProto_inBounds (buf : List AbstractByteProto) (off : Nat)
    (patch : List AbstractByteProto) (h : off + patch.length ≤ buf.length) :
    writeBytesProto buf off patch =
      some (buf.take off ++ patch ++ buf.drop (off + patch.length)) := by
  simp only [writeBytesProto, Nat.ble_eq_true_of_le h]

/-- **Untyped copies never fault on byte values (universal).** -/
theorem copyNonOverlappingBytesProto_inBounds (src dst : List AbstractByteProto)
    (srcOff dstOff len : Nat) (hs : srcOff + len ≤ src.length) (hd : dstOff + len ≤ dst.length) :
    copyNonOverlappingBytesProto src dst srcOff dstOff len =
      some (dst.take dstOff ++ (src.drop srcOff).take len ++
        dst.drop (dstOff + ((src.drop srcOff).take len).length)) := by
  have hlen : ((src.drop srcOff).take len).length = len := by
    simp only [List.length_take, List.length_drop]
    exact Nat.min_eq_left (Nat.le_sub_of_add_le' hs)
  simp only [copyNonOverlappingBytesProto, readBytesProto, Nat.ble_eq_true_of_le hs]
  exact writeBytesProto_inBounds dst dstOff _ (by rw [hlen]; exact hd)

/-- **`write_bytes` never faults on the fill value (universal).** -/
theorem writeBytesFillProto_inBounds (buf : List AbstractByteProto) (off : Nat) (val : UInt8)
    (count : Nat) (h : off + count ≤ buf.length) :
    writeBytesFillProto buf off val count =
      some (buf.take off ++ List.replicate count (mkInitByte val) ++ buf.drop (off + count)) := by
  have := writeBytesProto_inBounds buf off (List.replicate count (mkInitByte val))
    (by rw [List.length_replicate]; exact h)
  rw [List.length_replicate] at this
  exact this

theorem decodePlainInt_byte (b : UInt8) :
    decodePlainIntProto 1 [mkInitByte b] = some (.scalar b.toNat 1) := by
  simp [decodePlainIntProto, mkInitByte, abstractBytesHaveFragProto, dataBytesProto, leValue]

/-- **Read-time `bool` validity (universal over the byte value).** -/
theorem readBool_byte (ptrBytes : Nat) (b : UInt8) :
    decodeTypedValueFromBytesProto ptrBytes .bool [mkInitByte b] =
      match Nat.ble b.toNat 1 with
      | true => some (.scalar b.toNat 1)
      | false => none := by
  simp only [decodeTypedValueFromBytesProto, decodePlainInt_byte]

theorem ble_one_false_of_two_le (v : Nat) (hv : 2 ≤ v) : Nat.ble v 1 = false := by
  cases h : Nat.ble v 1 with
  | false => rfl
  | true => exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt hv)

/-- **Invalid `bool` bytes fault only when read as `bool` (universal, `b ≥ 2`).** -/
theorem readBool_invalid_none (ptrBytes : Nat) (b : UInt8) (hb : 2 ≤ b.toNat) :
    decodeTypedValueFromBytesProto ptrBytes .bool [mkInitByte b] = none := by
  rw [readBool_byte, ble_one_false_of_two_le _ hb]

/-- **`Unaligned<bool>` enforces the same read-time validity (universal).** -/
theorem readUnalignedBool_invalid_none (ptrBytes : Nat) (b : UInt8) (hb : 2 ≤ b.toNat) :
    decodeTypedValueFromBytesProto ptrBytes (.unaligned .bool) [mkInitByte b] = none := by
  simp only [decodeTypedValueFromBytesProto, decodePlainInt_byte, ble_one_false_of_two_le _ hb]

/-- **`MaybeUninit<T>` reads never inspect validity (universal):** any byte image of the
right width, including uninitialized and invalid bytes, is a valid `MaybeUninit<T>`. -/
theorem readMaybeUninit_any (ptrBytes : Nat) (inner : TyProto) (bytes : List AbstractByteProto)
    (h : bytes.length = inner.sizeBytes ptrBytes) :
    decodeTypedValueFromBytesProto ptrBytes (.maybeUninit inner) bytes = some (.rawBytes bytes) := by
  simp only [decodeTypedValueFromBytesProto, h, Nat.beq_refl]

/-- **`u8` reads accept every initialized plain byte (universal).** -/
theorem readU8_byte (ptrBytes : Nat) (b : UInt8) :
    decodeTypedValueFromBytesProto ptrBytes (.uint 1) [mkInitByte b] = some (.scalar b.toNat 1) :=
  decodePlainInt_byte b

/-! ## 10. Projections onto the live `AbstractByte` (both rustc snapshots) -/

def AbstractByteProto.toLive06 : AbstractByteProto →
    Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte
  | .uninit => .uninit
  | .init b fo => .init b (provPair? (.init b fo))

def AbstractByteProto.toLive08 : AbstractByteProto →
    Trusted.Rustc.V2026_08_01.MirSemantics.AbstractByte
  | .uninit => .uninit
  | .init b fo => .init b (provPair? (.init b fo))

/-- **Proto pointer encoding projects exactly onto live `encodeLittleEndianBytes` with
`(allocId, tag)` provenance (universal, `V2026_06_01`).** -/
theorem toLive06_encodeAux (a t o n bits idx k : Nat) :
    (encodePtrFragsAux a t o n bits idx k).map AbstractByteProto.toLive06 =
      Trusted.Rustc.V2026_06_01.MirSemantics.encodeLittleEndianBytes bits k (some (a, t)) := by
  induction k generalizing bits idx with
  | zero => rfl
  | succ k ih =>
    simp only [encodePtrFragsAux, List.map_cons, ih,
      Trusted.Rustc.V2026_06_01.MirSemantics.encodeLittleEndianBytes]
    rfl

/-- Same projection for `V2026_08_01` (universal). -/
theorem toLive08_encodeAux (a t o n bits idx k : Nat) :
    (encodePtrFragsAux a t o n bits idx k).map AbstractByteProto.toLive08 =
      Trusted.Rustc.V2026_08_01.MirSemantics.encodeLittleEndianBytes bits k (some (a, t)) := by
  induction k generalizing bits idx with
  | zero => rfl
  | succ k ih =>
    simp only [encodePtrFragsAux, List.map_cons, ih,
      Trusted.Rustc.V2026_08_01.MirSemantics.encodeLittleEndianBytes]
    rfl

theorem toLive06_encode (p : ProvenancePtrProto) (n : Nat) :
    (encodePtrBytesProto p n).map AbstractByteProto.toLive06 =
      Trusted.Rustc.V2026_06_01.MirSemantics.encodeLittleEndianBytes
        (normOffset n p.offsetBytes) n (some (p.allocId, p.tag)) :=
  toLive06_encodeAux _ _ _ _ _ _ _

theorem toLive08_encode (p : ProvenancePtrProto) (n : Nat) :
    (encodePtrBytesProto p n).map AbstractByteProto.toLive08 =
      Trusted.Rustc.V2026_08_01.MirSemantics.encodeLittleEndianBytes
        (normOffset n p.offsetBytes) n (some (p.allocId, p.tag)) :=
  toLive08_encodeAux _ _ _ _ _ _ _

/-! ## 11. Live `Trusted.Rustc.V2026_06_01.MirSemantics` witnesses -/

namespace LiveV06

open Trusted Trusted.Rustc.V2026_06_01.MirSemantics Trusted.Rustc.V2026_06_01.MirAst
  Trusted.Rustc.V2026_06_01.Layout

/-- Intact live pointer bytes produced by the real live encoder `encodeScalarBytes`
(every byte carries the same `(allocId, tag)` pair, no byte position). -/
def liveEnc (a t off n : Nat) : List AbstractByte :=
  match encodeScalarBytes ⟨off, n⟩ (some (a, t)) with
  | some bs => bs
  | none => []

/-- Plain (provenance-free) live integer bytes. -/
def livePlain (bits n : Nat) : List AbstractByte :=
  match encodeScalarBytes ⟨bits, n⟩ none with
  | some bs => bs
  | none => []

/-- Thin pointee used by the thin-pointer witnesses. -/
def thinTy : RigidTy := .uint .u8

/-- Live `decodePtrBytesNoForge` at a thin pointee. -/
def decodePtrBytesNoForgeLive (isRef : Bool) (ptrBytes : Nat) (bytes : List AbstractByte) :
    Option Value :=
  decodePtrBytesNoForge isRef thinTy ptrBytes bytes

def layouts64 : LayoutTable := { pointerBits := 64, isLittleEndian := true, entries := [] }
def layouts32 : LayoutTable := { pointerBits := 32, isLittleEndian := true, entries := [] }
def rawPtrTy : Ty := { kind := .rawPtr .not thinTy, layoutIdx := 0 }
def ptrScalarInit : ScalarLayout := .initialized (.pointer 0) ⟨1, 0xFFFFFFFFFFFFFFFF⟩
def ptrScalarUnion : ScalarLayout := .union (.pointer 0)

/-! ### W1: byte-reversed / permuted / duplicated pointers keep provenance (UNSOUND) -/

theorem w1_rev8_raw :
    decodePtrBytesNoForge false thinTy 8 (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) := rfl

theorem w1_rev8_ref :
    decodePtrBytesNoForge true thinTy 8 (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) := rfl

/-- `offsetBytes = 0`: the reversed image is byte-for-byte identical, so no data check can
detect the reversal; only per-byte positions can. -/
theorem w1_rev8_zero_ref :
    decodePtrBytesNoForge true thinTy 8 (liveEnc 1 1 0 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0 } 8) := rfl

theorem w1_rev4_raw :
    decodePtrBytesNoForge false thinTy 4 (liveEnc 1 1 0x11223344 4).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x44332211 } 4) := rfl

theorem w1_rev4_ref :
    decodePtrBytesNoForge true thinTy 4 (liveEnc 1 1 0x11223344 4).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x44332211 } 4) := rfl

theorem w1_swap01_ref :
    decodePtrBytesNoForge true thinTy 8 (swapFirstTwo (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2211 } 8) := rfl

theorem w1_swap01_raw :
    decodePtrBytesNoForge false thinTy 8 (swapFirstTwo (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2211 } 8) := rfl

theorem w1_dup0_ref :
    decodePtrBytesNoForge true thinTy 8 (dupFirstByte (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2222222222222222 } 8) := rfl

theorem w1_dup0_raw :
    decodePtrBytesNoForge false thinTy 8 (dupFirstByte (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2222222222222222 } 8) := rfl

theorem w1_scalarInit_rev8 :
    decodeScalarLayoutBytesNoForge ptrScalarInit (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) := rfl

theorem w1_scalarUnion_rev8 :
    decodeScalarLayoutBytesNoForge ptrScalarUnion (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) := rfl

theorem w1_scalarInit_swap01 :
    decodeScalarLayoutBytesNoForge ptrScalarInit (swapFirstTwo (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2211 } 8) := rfl

theorem w1_scalarUnion_dup0 :
    decodeScalarLayoutBytesNoForge ptrScalarUnion (dupFirstByte (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2222222222222222 } 8) := rfl

theorem w1_typed_rawPtr_rev8_64bit :
    decodeTypedValueFromBytes 16 layouts64 rawPtrTy (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) := rfl

theorem w1_typed_rawPtr_rev4_32bit :
    decodeTypedValueFromBytes 16 layouts32 rawPtrTy (liveEnc 1 1 0x11223344 4).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x44332211 } 4) := rfl

/-! ### W2: same-`(allocId, tag)` offset splicing keeps provenance (UNSOUND, `UCG#558`) -/

/-- Byte `0` of `p = 0` with bytes `1..7` of `p + 4`: the spliced data equals `p`. -/
theorem w2_splice_0_4_ref :
    decodePtrBytesNoForge true thinTy 8 (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 4 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0 } 8) := rfl

theorem w2_splice_10_14_ref :
    decodePtrBytesNoForge true thinTy 8
      (spliceBytes 1 (liveEnc 1 1 0x10 8) (liveEnc 1 1 0x14 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x10 } 8) := rfl

/-- `p = 0` vs `p + 256`: byte `0` is `0x00` in both, so the splice is byte-identical to
`p + 256`; only the originating image identity distinguishes it. -/
theorem w2_splice_0_256_ref :
    decodePtrBytesNoForge true thinTy 8 (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 256 8)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 8) := rfl

theorem w2_splice_0_256_raw :
    decodePtrBytesNoForge false thinTy 8 (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 256 8)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 8) := rfl

theorem w2_splice_0_256_rev4_ref :
    decodePtrBytesNoForge true thinTy 4 (spliceBytes 1 (liveEnc 1 1 0 4) (liveEnc 1 1 256 4)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 4) := rfl

theorem w2_scalarInit_splice_0_256 :
    decodeScalarLayoutBytesNoForge ptrScalarInit
      (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 256 8)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 8) := rfl

theorem w2_scalarUnion_splice_10_14 :
    decodeScalarLayoutBytesNoForge ptrScalarUnion
      (spliceBytes 1 (liveEnc 1 1 0x10 8) (liveEnc 1 1 0x14 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x10 } 8) := rfl

/-! ### W3: wide pointer halves and `ProvenancePtr.tag` -/

/-- `&dyn Trait` with byte-reversed vtable half keeps vtable provenance (UNSOUND). -/
theorem w3_dyn_rev_vtable_ref :
    decodePtrBytesNoForge true (.dynamic "Trait") 8
      (liveEnc 1 1 0x10 8 ++ (liveEnc 2 2 0x1122 8).reverse) =
      some (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8,
        .ptr { allocId := 2, offsetBytes := 0x2211000000000000 } 8]) := rfl

theorem w3_dyn_rev_vtable_raw :
    decodePtrBytesNoForge false (.dynamic "Trait") 8
      (liveEnc 1 1 0x10 8 ++ (liveEnc 2 2 0x1122 8).reverse) =
      some (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8,
        .ptr { allocId := 2, offsetBytes := 0x2211000000000000 } 8]) := rfl

/-- `&dyn Trait` with swapped (intact) halves: no forging, provenance follows the images. -/
theorem w3_dyn_swapped_halves_ref :
    decodePtrBytesNoForge true (.dynamic "Trait") 8 (liveEnc 2 2 0x40 8 ++ liveEnc 1 1 0x10 8) =
      some (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0x40 } 8,
        .ptr { allocId := 1, offsetBytes := 0x10 } 8]) := rfl

/-- `&[u8]` whose length half carries provenance is rejected (fail-closed). -/
theorem w3_slice_prov_len_ref :
    decodePtrBytesNoForge true (.slice thinTy) 8 (liveEnc 1 1 0x10 8 ++ liveEnc 2 2 3 8) = none :=
  rfl

/-- `*const [u8]` with swapped halves (length first) is rejected (fail-closed). -/
theorem w3_slice_swapped_raw :
    decodePtrBytesNoForge false (.slice thinTy) 8 (livePlain 3 8 ++ liveEnc 1 1 0x10 8) = none :=
  rfl

theorem w3_str_intact_ref :
    decodePtrBytesNoForge true .str 8 (liveEnc 1 1 0x10 8 ++ livePlain 3 8) =
      some (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8, .scalar ⟨3, 8⟩]) := rfl

/-- The byte provenance's second (`tag`) component is discarded on decode:
`ProvenancePtr` has no `tag` field and `ProvenancePtr.tag := allocId`. -/
theorem w3_tag_dropped_on_decode :
    decodePtrBytesNoForge true thinTy 8 (liveEnc 5 9 0x40 8) =
      some (.ptr { allocId := 5, offsetBytes := 0x40 } 8) ∧
    ProvenancePtr.tag { allocId := 5, offsetBytes := 0x40 } = 5 := ⟨rfl, rfl⟩

/-- Live encoders write `(allocId, tag) = (allocId, allocId)`, so honest round trips lose
nothing: the live `tag` is definitionally the `allocId`. -/
theorem w3_live_encode_writes_allocId_as_tag :
    encodeValueToBytes 16 layouts64 rawPtrTy (.ptr { allocId := 7, offsetBytes := 0x40 } 8) =
      some (liveEnc 7 7 0x40 8) ∧
    decodePtrBytesNoForge false thinTy 8 (liveEnc 7 7 0x40 8) =
      some (.ptr { allocId := 7, offsetBytes := 0x40 } 8) := ⟨rfl, rfl⟩

/-- Mixed tags under one `allocId` are stripped (live checks both pair components). -/
theorem w3_mixed_tag_stripped_ref :
    decodePtrBytesNoForge true thinTy 8 (spliceBytes 4 (liveEnc 5 9 0x40 8) (liveEnc 5 10 0x40 8)) =
      none := rfl

/-! ### `Kani#5205` / `#5196`: read-time untyped-byte validity audit -/

def tl (sz al : Nat) (br : BackendRepr) (f : FieldsShape) (fl : List Nat) : TypeLayout :=
  { size := ⟨sz⟩, align := ⟨al⟩, backendRepr := br, fields := f, variants := .single 0,
    isUninhabited := false, fieldLayouts := fl }

def boolSL : ScalarLayout := .initialized (.int 8 false) ⟨0, 1⟩
def u8SL : ScalarLayout := .initialized (.int 8 false) ⟨0, 255⟩

/-- Layouts: `0 [u8; 1]`, `1 MaybeUninit<bool>`, `2 ()`, `3 bool`, `4 u8`,
`5 Unaligned<bool>` (`#[repr(packed)]`, align 1), `6 MaybeUninit<Unaligned<bool>>`,
`7 [u8; 4]`, `8 char`, `9 u32`. -/
def kLayouts : LayoutTable := { pointerBits := 64, isLittleEndian := true, entries := [
  tl 1 1 .memory (.array ⟨1⟩ 1) [4],
  tl 1 1 .memory (.union 2) [2, 3],
  tl 0 1 .memory (.arbitrary [] []) [],
  tl 1 1 (.scalar boolSL) .primitive [],
  tl 1 1 (.scalar u8SL) .primitive [],
  tl 1 1 (.scalar boolSL) (.arbitrary [⟨0⟩] [0]) [3],
  tl 1 1 .memory (.union 2) [2, 5],
  tl 4 1 .memory (.array ⟨1⟩ 4) [4],
  tl 4 4 (.scalar (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩)) .primitive [],
  tl 4 4 (.scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩)) .primitive []] }

def tyU8A1 : Ty := { kind := .array (.uint .u8) 1, layoutIdx := 0 }
def tyMUBool : Ty := { kind := .adt "core::mem::MaybeUninit" [.bool], layoutIdx := 1 }
def tyUnit : Ty := { kind := .tuple [], layoutIdx := 2 }
def tyBool : Ty := { kind := .bool, layoutIdx := 3 }
def tyU8 : Ty := { kind := .uint .u8, layoutIdx := 4 }
def tyUnalBool : Ty := { kind := .adt "Unaligned" [.bool], layoutIdx := 5 }
def tyMUUnal : Ty :=
  { kind := .adt "core::mem::MaybeUninit" [.adt "Unaligned" [.bool]], layoutIdx := 6 }
def tyU8A4 : Ty := { kind := .array (.uint .u8) 4, layoutIdx := 7 }
def tyChar : Ty := { kind := .char, layoutIdx := 8 }
def tyU32 : Ty := { kind := .uint .u32, layoutIdx := 9 }
def tyPtrU8 : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }

theorem k_decode_bool_2_none : decodeTypedValueFromBytes 16 kLayouts tyBool [.init 2 none] = none :=
  rfl

theorem k_decode_u8_2 :
    decodeTypedValueFromBytes 16 kLayouts tyU8 [.init 2 none] = some (.scalar ⟨2, 1⟩) := rfl

/-- `MaybeUninit<bool>` holding `2u8` decodes (raw-byte overlay), no validity check. -/
theorem k_decode_maybeUninitBool_2 :
    decodeTypedValueFromBytes 16 kLayouts tyMUBool [.init 2 none] =
      some (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]]) := rfl

theorem k_decode_unalignedBool_2_none :
    decodeTypedValueFromBytes 16 kLayouts tyUnalBool [.init 2 none] = none := rfl

theorem k_decode_unalignedBool_1 :
    decodeTypedValueFromBytes 16 kLayouts tyUnalBool [.init 1 none] =
      some (.aggregate 0 [.scalar ⟨1, 1⟩]) := rfl

/-- `Unaligned<bool>` read at unaligned byte offset `1` of a `[u8; 4]` buffer. -/
theorem k_decode_unalignedBool_offset1 :
    (match sliceAbstractBytes [.init 7 none, .init 1 none, .init 9 none, .init 9 none] 1 1 with
      | some bs => decodeTypedValueFromBytes 16 kLayouts tyUnalBool bs
      | none => none) = some (.aggregate 0 [.scalar ⟨1, 1⟩]) := rfl

theorem k_decode_maybeUninitUnaligned_2 :
    decodeTypedValueFromBytes 16 kLayouts tyMUUnal [.init 2 none] =
      some (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]]) := rfl

/-- `char` surrogate `0xD800` bytes: typed `char` read faults, `u32` read succeeds. -/
theorem k_decode_char_surrogate :
    decodeTypedValueFromBytes 16 kLayouts tyChar (livePlain 0xD800 4) = none ∧
    decodeTypedValueFromBytes 16 kLayouts tyU32 (livePlain 0xD800 4) = some (.scalar ⟨0xD800, 4⟩) :=
  ⟨rfl, rfl⟩

/-- Observable outcome of one live MIR step. -/
inductive StepOutcome : Type where
  | step (active : List LocalSlot) (callers : List (List LocalSlot)) : StepOutcome
  | ub : StepOutcome
  | unsupported : StepOutcome
  | other : StepOutcome

def stepOutcome : MirStepNode → StepOutcome
  | .tau (.running s) => .step s.frame.locals (s.memory.callStack.map (fun f => f.frame.locals))
  | .vis (.inl (.fail .ub)) _ => .ub
  | .vis (.inl (.fail .unsupported)) _ => .unsupported
  | _ => .other

/-- Observable outcome of a live operand read. -/
inductive ReadOutcome : Type where
  | ok (v : Value) : ReadOutcome
  | ub : ReadOutcome
  | unsupported : ReadOutcome

def readOutcome : PlaceReadResult → ReadOutcome
  | .ok v _ => .ok v
  | .ub => .ub
  | .unsupported => .unsupported

def decl (t : Ty) : LocalDecl := { mutability := .mut, ty := t, debugName := none }
def lc (i : Nat) : Place := { local_ := i, projection := [] }
def usz (n : Nat) : Operand :=
  .constant { ty := { kind := .uint .usize, layoutIdx := 0 }, val := .scalar (.int ⟨n, 8⟩) }

/-- Active-frame state: `_1` source, `_2` destination, `_3 : *const u8 → _1`,
`_4 : *mut u8 → _2`. -/
def activeState (srcSlot dstSlot : LocalSlot) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init .unit, srcSlot, dstSlot,
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 2, offsetBytes := 0 } 8)] },
    memory := { emptyMemory with
      borrows := [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .unique },
        { tag := 2, targetLocal := 2, targetProjection := [], perm := .unique }],
      nextTag := 3 } }

/-- `copy_nonoverlapping::<u8>(_3, _4, 1)` within the active frame. -/
def copyActive (srcTy dstTy : Ty) (srcSlot dstSlot : LocalSlot) : MirStepNode :=
  evalCopyNonOverlapping (activeState srcSlot dstSlot) (.copy (lc 3)) (.copy (lc 4)) (usz 1)
    [decl tyUnit, decl srcTy, decl dstTy, decl tyPtrU8, decl tyPtrU8] kLayouts

def u8Arr2 : LocalSlot := .init (.aggregate 0 [.scalar ⟨2, 1⟩])
def u8Scalar2 : LocalSlot := .init (.scalar ⟨2, 1⟩)

def activeLocals (dst : LocalSlot) (src : LocalSlot := u8Arr2) : List LocalSlot :=
  [.init .unit, src, dst, .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
    .init (.ptr { allocId := 2, offsetBytes := 0 } 8)]

theorem k_copy_u8arr_to_maybeUninitBool :
    stepOutcome (copyActive tyU8A1 tyMUBool u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.unit, .scalar ⟨2, 1⟩]))) [] := rfl

theorem k_copy_u8arr_to_u8arr :
    stepOutcome (copyActive tyU8A1 tyU8A1 u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.scalar ⟨2, 1⟩]))) [] := rfl

theorem k_copy_maybeUninit_to_maybeUninit :
    stepOutcome (copyActive tyMUBool tyMUBool
      (.init (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]])) .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.unit, .scalar ⟨2, 1⟩]))
        (.init (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]]))) [] := rfl

/-- Premature write-time UB: an untyped `u8` copy into a `bool` local (conservative). -/
theorem k_copy_u8arr_to_bool_premature_ub :
    stepOutcome (copyActive tyU8A1 tyBool u8Arr2 .uninit) = .ub := rfl

theorem k_copy_u8_to_bool_premature_ub :
    stepOutcome (copyActive tyU8 tyBool u8Scalar2 .uninit) = .ub := rfl

/-- The copy into `Unaligned<bool>` stores an invalid `bool` field without any check. -/
theorem k_copy_u8arr_to_unalignedBool :
    stepOutcome (copyActive tyU8A1 tyUnalBool u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.scalar ⟨2, 1⟩]))) [] := rfl

theorem k_copy_u8arr_to_maybeUninitUnaligned :
    stepOutcome (copyActive tyU8A1 tyMUUnal u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.unit, .aggregate 0 [.scalar ⟨2, 1⟩]]))) [] := rfl

/-- Copy, then read place `_2` with projection `proj` from the resulting active frame. -/
def copyThenRead (srcTy dstTy : Ty) (srcSlot : LocalSlot) (proj : List ProjectionElem) :
    ReadOutcome :=
  match stepOutcome (copyActive srcTy dstTy srcSlot .uninit) with
  | .step locals _ =>
    readOutcome (evalOperand locals (.copy { local_ := 2, projection := proj }) [] [] kLayouts []
      [decl tyUnit, decl srcTy, decl dstTy, decl tyPtrU8, decl tyPtrU8] [])
  | _ => .unsupported

/-- **GAP (permissive, `Kani#5205`):** after the untyped copy of `2u8` into `Unaligned<bool>`,
reading field `.0 : bool` yields the invalid `bool` `2` without UB. -/
theorem k_gap_unalignedBool_field_reads_2 :
    copyThenRead tyU8A1 tyUnalBool u8Arr2 [.field 0 tyBool] = .ok (.scalar ⟨2, 1⟩) := rfl

/-- **GAP:** reading the whole `Unaligned<bool>` (a typed copy) also succeeds without UB. -/
theorem k_gap_unalignedBool_whole_reads_2 :
    copyThenRead tyU8A1 tyUnalBool u8Arr2 [] = .ok (.aggregate 0 [.scalar ⟨2, 1⟩]) := rfl

/-- **GAP:** `MaybeUninit<Unaligned<bool>>::assume_init` (field `.1`) yields an invalid
`Unaligned<bool>` without UB. -/
theorem k_gap_maybeUninitUnaligned_assume_init :
    copyThenRead tyU8A1 tyMUUnal u8Arr2 [.field 1 tyUnalBool] =
      .ok (.aggregate 0 [.scalar ⟨2, 1⟩]) := rfl

/-- Correct read-time UB: `MaybeUninit<bool>::assume_init` (field `.1 : bool`) on `2u8`. -/
theorem k_maybeUninitBool_assume_init_ub :
    copyThenRead tyU8A1 tyMUBool u8Arr2 [.field 1 tyBool] = .ub := rfl

theorem k_maybeUninitUnaligned_inner_field_ub :
    copyThenRead tyU8A1 tyMUUnal u8Arr2 [.field 1 tyUnalBool, .field 0 tyBool] = .ub := rfl

/-- Root `bool` locals are not re-validated on `Operand.copy`. -/
theorem k_bool_local_holding_2_reads_ok :
    readOutcome (evalOperand [.init .unit, .uninit, .init (.scalar ⟨2, 1⟩)] (.copy (lc 2)) [] []
      kLayouts [] [decl tyUnit, decl tyU8A1, decl tyBool] []) = .ok (.scalar ⟨2, 1⟩) := rfl

def wFnAbi : FnAbi :=
  { args := [], ret := { layout := tl 0 1 .memory (.arbitrary [] []) [], mode := .direct },
    conv := .rust, canUnwind := false }

def callerBody (dstTy : Ty) : CapturedMir :=
  { defPath := "caller", argCount := 0, localDecls := [decl tyUnit, decl dstTy],
    basicBlocks := [], phase := .runtimePostCleanup, role := .subject, fnAbi := wFnAbi,
    layouts := kLayouts, allocations := [] }

/-- Foreign-frame state: the destination `_1` lives in the caller frame (depth `0`). -/
def foreignState (srcSlot dstSlot : LocalSlot) (dstTy : Ty) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init .unit, srcSlot, .uninit,
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 2, offsetBytes := 0 } 8)] },
    memory := { emptyMemory with
      borrows := [
        { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique,
          targetFrameDepth := 1 },
        { tag := 2, targetLocal := 1, targetProjection := [], perm := .unique,
          targetFrameDepth := 0 }],
      nextTag := 3,
      callStack := [
        { callerBody := callerBody dstTy,
          frame := { blockIdx := 0, stmtIdx := 0, locals := [.init .unit, dstSlot] },
          destination := lc 0 }] } }

def copyForeign (srcTy dstTy : Ty) (srcSlot dstSlot : LocalSlot) : MirStepNode :=
  evalCopyNonOverlapping (foreignState srcSlot dstSlot dstTy) (.copy (lc 3)) (.copy (lc 4))
    (usz 1) [decl tyUnit, decl srcTy, decl tyUnit, decl tyPtrU8, decl tyPtrU8] kLayouts

def foreignActive (src : LocalSlot) : List LocalSlot :=
  [.init .unit, src, .uninit, .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
    .init (.ptr { allocId := 2, offsetBytes := 0 } 8)]

/-- **GAP (permissive):** a foreign-frame `copy_nonoverlapping` of `2u8` into the caller's
`bool` local stores `2` with no check (the active-frame path reports premature UB). -/
theorem k_gap_foreign_u8_to_bool_stores_2 :
    stepOutcome (copyForeign tyU8 tyBool u8Scalar2 .uninit) =
      .step (foreignActive u8Scalar2) [[.init .unit, .init (.scalar ⟨2, 1⟩)]] := rfl

/-- Foreign-frame copy of a `[u8; 1]` value into a caller `bool` stores an array value. -/
theorem k_gap_foreign_u8arr_to_bool_stores_array :
    stepOutcome (copyForeign tyU8A1 tyBool u8Arr2 .uninit) =
      .step (foreignActive u8Arr2) [[.init .unit, .init (.aggregate 0 [.scalar ⟨2, 1⟩])]] := rfl

/-- Foreign-frame copy into a caller `MaybeUninit<bool>` stores the raw source value. -/
theorem k_foreign_u8_to_maybeUninitBool :
    stepOutcome (copyForeign tyU8 tyMUBool u8Scalar2 .uninit) =
      .step (foreignActive u8Scalar2) [[.init .unit, .init (.scalar ⟨2, 1⟩)]] := rfl

/-- `write_bytes::<T>(dst, val, 1)` against `_2` of type `dstTy`. -/
inductive WriteOutcome : Type where
  | ub : WriteOutcome
  | unsupported : WriteOutcome
  | noWrite : WriteOutcome
  | store (v : Value) : WriteOutcome
  | other : WriteOutcome

def writeBytesOutcome (dstTy : Ty) (elem : RigidTy) (v : Nat) : WriteOutcome :=
  match writeBytesAction [{ tag := 2, targetLocal := 2, targetProjection := [], perm := .unique }]
      0 { defPath := "core::intrinsics::write_bytes", typeArgs := [elem] }
      [decl tyUnit, decl tyU8A1, decl dstTy, decl tyPtrU8, decl tyPtrU8] kLayouts
      [.copy (lc 4), .constant { ty := tyU8, val := .scalar (.int ⟨v, 1⟩) }, usz 1]
      [.ptr { allocId := 2, offsetBytes := 0 } 8, .scalar ⟨v, 1⟩, .scalar ⟨1, 8⟩] with
  | .fault .ub => .ub
  | .fault .unsupported => .unsupported
  | .noWrite => .noWrite
  | .store _ _ _ v => .store v
  | _ => .other

theorem k_writeBytes_bool_2_unsupported : writeBytesOutcome tyBool .bool 2 = .unsupported := rfl
theorem k_writeBytes_bool_1_store : writeBytesOutcome tyBool .bool 1 = .store (.scalar ⟨1, 1⟩) :=
  rfl
theorem k_writeBytes_maybeUninitBool_unsupported :
    writeBytesOutcome tyMUBool tyMUBool.kind 2 = .unsupported := rfl
theorem k_writeBytes_u8arr_unsupported : writeBytesOutcome tyU8A1 (.uint .u8) 2 = .unsupported :=
  rfl
theorem k_writeBytes_u8_store : writeBytesOutcome tyU8 (.uint .u8) 2 = .store (.scalar ⟨2, 1⟩) :=
  rfl
theorem k_writeBytes_unalignedBool_unsupported :
    writeBytesOutcome tyUnalBool tyUnalBool.kind 2 = .unsupported := rfl
theorem k_writeBytes_char_ff_unsupported : writeBytesOutcome tyChar .char 0xFF = .unsupported :=
  rfl


/-! ### Prototype on the same inputs: stripped where live retains -/

/-- The prototype bytes project exactly onto the live encoder's bytes. -/
theorem proto_projects_to_liveEnc :
    (encodePtrBytesProto ⟨1, 1, 0x1122334455667788⟩ 8).map AbstractByteProto.toLive06 =
      liveEnc 1 1 0x1122334455667788 8 := rfl

end LiveV06

/-! ## 11b. Live `Trusted.Rustc.V2026_08_01.MirSemantics` witnesses (parity) -/

namespace LiveV08

open Trusted Trusted.Rustc.V2026_08_01.MirSemantics Trusted.Rustc.V2026_08_01.MirAst
  Trusted.Rustc.V2026_08_01.Layout

/-- Intact live pointer bytes produced by the real live encoder `encodeScalarBytes`
(every byte carries the same `(allocId, tag)` pair, no byte position). -/
def liveEnc (a t off n : Nat) : List AbstractByte :=
  match encodeScalarBytes ⟨off, n⟩ (some (a, t)) with
  | some bs => bs
  | none => []

/-- Plain (provenance-free) live integer bytes. -/
def livePlain (bits n : Nat) : List AbstractByte :=
  match encodeScalarBytes ⟨bits, n⟩ none with
  | some bs => bs
  | none => []

/-- Thin pointee used by the thin-pointer witnesses. -/
def thinTy : RigidTy := .uint .u8

/-- Live `decodePtrBytesNoForge` at a thin pointee. -/
def decodePtrBytesNoForgeLive (isRef : Bool) (ptrBytes : Nat) (bytes : List AbstractByte) :
    Option Value :=
  decodePtrBytesNoForge isRef thinTy ptrBytes bytes

def layouts64 : LayoutTable := { pointerBits := 64, isLittleEndian := true, entries := [] }
def layouts32 : LayoutTable := { pointerBits := 32, isLittleEndian := true, entries := [] }
def rawPtrTy : Ty := { kind := .rawPtr .not thinTy, layoutIdx := 0 }
def ptrScalarInit : ScalarLayout := .initialized (.pointer 0) ⟨1, 0xFFFFFFFFFFFFFFFF⟩
def ptrScalarUnion : ScalarLayout := .union (.pointer 0)

/-! ### W1: byte-reversed / permuted / duplicated pointers keep provenance (UNSOUND) -/

theorem w1_rev8_raw :
    decodePtrBytesNoForge false thinTy 8 (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) := rfl

theorem w1_rev8_ref :
    decodePtrBytesNoForge true thinTy 8 (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) := rfl

/-- `offsetBytes = 0`: the reversed image is byte-for-byte identical, so no data check can
detect the reversal; only per-byte positions can. -/
theorem w1_rev8_zero_ref :
    decodePtrBytesNoForge true thinTy 8 (liveEnc 1 1 0 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0 } 8) := rfl

theorem w1_rev4_raw :
    decodePtrBytesNoForge false thinTy 4 (liveEnc 1 1 0x11223344 4).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x44332211 } 4) := rfl

theorem w1_rev4_ref :
    decodePtrBytesNoForge true thinTy 4 (liveEnc 1 1 0x11223344 4).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x44332211 } 4) := rfl

theorem w1_swap01_ref :
    decodePtrBytesNoForge true thinTy 8 (swapFirstTwo (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2211 } 8) := rfl

theorem w1_swap01_raw :
    decodePtrBytesNoForge false thinTy 8 (swapFirstTwo (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2211 } 8) := rfl

theorem w1_dup0_ref :
    decodePtrBytesNoForge true thinTy 8 (dupFirstByte (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2222222222222222 } 8) := rfl

theorem w1_dup0_raw :
    decodePtrBytesNoForge false thinTy 8 (dupFirstByte (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2222222222222222 } 8) := rfl

theorem w1_scalarInit_rev8 :
    decodeScalarLayoutBytesNoForge ptrScalarInit (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) := rfl

theorem w1_scalarUnion_rev8 :
    decodeScalarLayoutBytesNoForge ptrScalarUnion (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) := rfl

theorem w1_scalarInit_swap01 :
    decodeScalarLayoutBytesNoForge ptrScalarInit (swapFirstTwo (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2211 } 8) := rfl

theorem w1_scalarUnion_dup0 :
    decodeScalarLayoutBytesNoForge ptrScalarUnion (dupFirstByte (liveEnc 1 1 0x1122 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x2222222222222222 } 8) := rfl

theorem w1_typed_rawPtr_rev8_64bit :
    decodeTypedValueFromBytes 16 layouts64 rawPtrTy (liveEnc 1 1 0x1122334455667788 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x8877665544332211 } 8) := rfl

theorem w1_typed_rawPtr_rev4_32bit :
    decodeTypedValueFromBytes 16 layouts32 rawPtrTy (liveEnc 1 1 0x11223344 4).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0x44332211 } 4) := rfl

/-! ### W2: same-`(allocId, tag)` offset splicing keeps provenance (UNSOUND, `UCG#558`) -/

/-- Byte `0` of `p = 0` with bytes `1..7` of `p + 4`: the spliced data equals `p`. -/
theorem w2_splice_0_4_ref :
    decodePtrBytesNoForge true thinTy 8 (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 4 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0 } 8) := rfl

theorem w2_splice_10_14_ref :
    decodePtrBytesNoForge true thinTy 8
      (spliceBytes 1 (liveEnc 1 1 0x10 8) (liveEnc 1 1 0x14 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x10 } 8) := rfl

/-- `p = 0` vs `p + 256`: byte `0` is `0x00` in both, so the splice is byte-identical to
`p + 256`; only the originating image identity distinguishes it. -/
theorem w2_splice_0_256_ref :
    decodePtrBytesNoForge true thinTy 8 (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 256 8)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 8) := rfl

theorem w2_splice_0_256_raw :
    decodePtrBytesNoForge false thinTy 8 (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 256 8)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 8) := rfl

theorem w2_splice_0_256_rev4_ref :
    decodePtrBytesNoForge true thinTy 4 (spliceBytes 1 (liveEnc 1 1 0 4) (liveEnc 1 1 256 4)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 4) := rfl

theorem w2_scalarInit_splice_0_256 :
    decodeScalarLayoutBytesNoForge ptrScalarInit
      (spliceBytes 1 (liveEnc 1 1 0 8) (liveEnc 1 1 256 8)) =
      some (.ptr { allocId := 1, offsetBytes := 256 } 8) := rfl

theorem w2_scalarUnion_splice_10_14 :
    decodeScalarLayoutBytesNoForge ptrScalarUnion
      (spliceBytes 1 (liveEnc 1 1 0x10 8) (liveEnc 1 1 0x14 8)) =
      some (.ptr { allocId := 1, offsetBytes := 0x10 } 8) := rfl

/-! ### W3: wide pointer halves and `ProvenancePtr.tag` -/

/-- `&dyn Trait` with byte-reversed vtable half keeps vtable provenance (UNSOUND). -/
theorem w3_dyn_rev_vtable_ref :
    decodePtrBytesNoForge true (.dynamic "Trait") 8
      (liveEnc 1 1 0x10 8 ++ (liveEnc 2 2 0x1122 8).reverse) =
      some (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8,
        .ptr { allocId := 2, offsetBytes := 0x2211000000000000 } 8]) := rfl

theorem w3_dyn_rev_vtable_raw :
    decodePtrBytesNoForge false (.dynamic "Trait") 8
      (liveEnc 1 1 0x10 8 ++ (liveEnc 2 2 0x1122 8).reverse) =
      some (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8,
        .ptr { allocId := 2, offsetBytes := 0x2211000000000000 } 8]) := rfl

/-- `&dyn Trait` with swapped (intact) halves: no forging, provenance follows the images. -/
theorem w3_dyn_swapped_halves_ref :
    decodePtrBytesNoForge true (.dynamic "Trait") 8 (liveEnc 2 2 0x40 8 ++ liveEnc 1 1 0x10 8) =
      some (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0x40 } 8,
        .ptr { allocId := 1, offsetBytes := 0x10 } 8]) := rfl

/-- `&[u8]` whose length half carries provenance is rejected (fail-closed). -/
theorem w3_slice_prov_len_ref :
    decodePtrBytesNoForge true (.slice thinTy) 8 (liveEnc 1 1 0x10 8 ++ liveEnc 2 2 3 8) = none :=
  rfl

/-- `*const [u8]` with swapped halves (length first) is rejected (fail-closed). -/
theorem w3_slice_swapped_raw :
    decodePtrBytesNoForge false (.slice thinTy) 8 (livePlain 3 8 ++ liveEnc 1 1 0x10 8) = none :=
  rfl

theorem w3_str_intact_ref :
    decodePtrBytesNoForge true .str 8 (liveEnc 1 1 0x10 8 ++ livePlain 3 8) =
      some (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0x10 } 8, .scalar ⟨3, 8⟩]) := rfl

/-- The byte provenance's second (`tag`) component is discarded on decode:
`ProvenancePtr` has no `tag` field and `ProvenancePtr.tag := allocId`. -/
theorem w3_tag_dropped_on_decode :
    decodePtrBytesNoForge true thinTy 8 (liveEnc 5 9 0x40 8) =
      some (.ptr { allocId := 5, offsetBytes := 0x40 } 8) ∧
    ProvenancePtr.tag { allocId := 5, offsetBytes := 0x40 } = 5 := ⟨rfl, rfl⟩

/-- Live encoders write `(allocId, tag) = (allocId, allocId)`, so honest round trips lose
nothing: the live `tag` is definitionally the `allocId`. -/
theorem w3_live_encode_writes_allocId_as_tag :
    encodeValueToBytes 16 layouts64 rawPtrTy (.ptr { allocId := 7, offsetBytes := 0x40 } 8) =
      some (liveEnc 7 7 0x40 8) ∧
    decodePtrBytesNoForge false thinTy 8 (liveEnc 7 7 0x40 8) =
      some (.ptr { allocId := 7, offsetBytes := 0x40 } 8) := ⟨rfl, rfl⟩

/-- Mixed tags under one `allocId` are stripped (live checks both pair components). -/
theorem w3_mixed_tag_stripped_ref :
    decodePtrBytesNoForge true thinTy 8 (spliceBytes 4 (liveEnc 5 9 0x40 8) (liveEnc 5 10 0x40 8)) =
      none := rfl

/-! ### `Kani#5205` / `#5196`: read-time untyped-byte validity audit -/

def tl (sz al : Nat) (br : BackendRepr) (f : FieldsShape) (fl : List Nat) : TypeLayout :=
  { size := ⟨sz⟩, align := ⟨al⟩, backendRepr := br, fields := f, variants := .single 0,
    isUninhabited := false, fieldLayouts := fl }

def boolSL : ScalarLayout := .initialized (.int 8 false) ⟨0, 1⟩
def u8SL : ScalarLayout := .initialized (.int 8 false) ⟨0, 255⟩

/-- Layouts: `0 [u8; 1]`, `1 MaybeUninit<bool>`, `2 ()`, `3 bool`, `4 u8`,
`5 Unaligned<bool>` (`#[repr(packed)]`, align 1), `6 MaybeUninit<Unaligned<bool>>`,
`7 [u8; 4]`, `8 char`, `9 u32`. -/
def kLayouts : LayoutTable := { pointerBits := 64, isLittleEndian := true, entries := [
  tl 1 1 .memory (.array ⟨1⟩ 1) [4],
  tl 1 1 .memory (.union 2) [2, 3],
  tl 0 1 .memory (.arbitrary [] []) [],
  tl 1 1 (.scalar boolSL) .primitive [],
  tl 1 1 (.scalar u8SL) .primitive [],
  tl 1 1 (.scalar boolSL) (.arbitrary [⟨0⟩] [0]) [3],
  tl 1 1 .memory (.union 2) [2, 5],
  tl 4 1 .memory (.array ⟨1⟩ 4) [4],
  tl 4 4 (.scalar (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩)) .primitive [],
  tl 4 4 (.scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩)) .primitive []] }

def tyU8A1 : Ty := { kind := .array (.uint .u8) 1, layoutIdx := 0 }
def tyMUBool : Ty := { kind := .adt "core::mem::MaybeUninit" [.bool], layoutIdx := 1 }
def tyUnit : Ty := { kind := .tuple [], layoutIdx := 2 }
def tyBool : Ty := { kind := .bool, layoutIdx := 3 }
def tyU8 : Ty := { kind := .uint .u8, layoutIdx := 4 }
def tyUnalBool : Ty := { kind := .adt "Unaligned" [.bool], layoutIdx := 5 }
def tyMUUnal : Ty :=
  { kind := .adt "core::mem::MaybeUninit" [.adt "Unaligned" [.bool]], layoutIdx := 6 }
def tyU8A4 : Ty := { kind := .array (.uint .u8) 4, layoutIdx := 7 }
def tyChar : Ty := { kind := .char, layoutIdx := 8 }
def tyU32 : Ty := { kind := .uint .u32, layoutIdx := 9 }
def tyPtrU8 : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }

theorem k_decode_bool_2_none : decodeTypedValueFromBytes 16 kLayouts tyBool [.init 2 none] = none :=
  rfl

theorem k_decode_u8_2 :
    decodeTypedValueFromBytes 16 kLayouts tyU8 [.init 2 none] = some (.scalar ⟨2, 1⟩) := rfl

/-- `MaybeUninit<bool>` holding `2u8` decodes (raw-byte overlay), no validity check. -/
theorem k_decode_maybeUninitBool_2 :
    decodeTypedValueFromBytes 16 kLayouts tyMUBool [.init 2 none] =
      some (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]]) := rfl

theorem k_decode_unalignedBool_2_none :
    decodeTypedValueFromBytes 16 kLayouts tyUnalBool [.init 2 none] = none := rfl

theorem k_decode_unalignedBool_1 :
    decodeTypedValueFromBytes 16 kLayouts tyUnalBool [.init 1 none] =
      some (.aggregate 0 [.scalar ⟨1, 1⟩]) := rfl

/-- `Unaligned<bool>` read at unaligned byte offset `1` of a `[u8; 4]` buffer. -/
theorem k_decode_unalignedBool_offset1 :
    (match sliceAbstractBytes [.init 7 none, .init 1 none, .init 9 none, .init 9 none] 1 1 with
      | some bs => decodeTypedValueFromBytes 16 kLayouts tyUnalBool bs
      | none => none) = some (.aggregate 0 [.scalar ⟨1, 1⟩]) := rfl

theorem k_decode_maybeUninitUnaligned_2 :
    decodeTypedValueFromBytes 16 kLayouts tyMUUnal [.init 2 none] =
      some (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]]) := rfl

/-- `char` surrogate `0xD800` bytes: typed `char` read faults, `u32` read succeeds. -/
theorem k_decode_char_surrogate :
    decodeTypedValueFromBytes 16 kLayouts tyChar (livePlain 0xD800 4) = none ∧
    decodeTypedValueFromBytes 16 kLayouts tyU32 (livePlain 0xD800 4) = some (.scalar ⟨0xD800, 4⟩) :=
  ⟨rfl, rfl⟩

/-- Observable outcome of one live MIR step. -/
inductive StepOutcome : Type where
  | step (active : List LocalSlot) (callers : List (List LocalSlot)) : StepOutcome
  | ub : StepOutcome
  | unsupported : StepOutcome
  | other : StepOutcome

def stepOutcome : MirStepNode → StepOutcome
  | .tau (.running s) => .step s.frame.locals (s.memory.callStack.map (fun f => f.frame.locals))
  | .vis (.inl (.fail .ub)) _ => .ub
  | .vis (.inl (.fail .unsupported)) _ => .unsupported
  | _ => .other

/-- Observable outcome of a live operand read. -/
inductive ReadOutcome : Type where
  | ok (v : Value) : ReadOutcome
  | ub : ReadOutcome
  | unsupported : ReadOutcome

def readOutcome : PlaceReadResult → ReadOutcome
  | .ok v _ => .ok v
  | .ub => .ub
  | .unsupported => .unsupported

def decl (t : Ty) : LocalDecl := { mutability := .mut, ty := t, debugName := none }
def lc (i : Nat) : Place := { local_ := i, projection := [] }
def usz (n : Nat) : Operand :=
  .constant { ty := { kind := .uint .usize, layoutIdx := 0 }, val := .scalar (.int ⟨n, 8⟩) }

/-- Active-frame state: `_1` source, `_2` destination, `_3 : *const u8 → _1`,
`_4 : *mut u8 → _2`. -/
def activeState (srcSlot dstSlot : LocalSlot) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init .unit, srcSlot, dstSlot,
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 2, offsetBytes := 0 } 8)] },
    memory := { emptyMemory with
      borrows := [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .unique },
        { tag := 2, targetLocal := 2, targetProjection := [], perm := .unique }],
      nextTag := 3 } }

/-- `copy_nonoverlapping::<u8>(_3, _4, 1)` within the active frame. -/
def copyActive (srcTy dstTy : Ty) (srcSlot dstSlot : LocalSlot) : MirStepNode :=
  evalCopyNonOverlapping (activeState srcSlot dstSlot) (.copy (lc 3)) (.copy (lc 4)) (usz 1)
    [decl tyUnit, decl srcTy, decl dstTy, decl tyPtrU8, decl tyPtrU8] kLayouts

def u8Arr2 : LocalSlot := .init (.aggregate 0 [.scalar ⟨2, 1⟩])
def u8Scalar2 : LocalSlot := .init (.scalar ⟨2, 1⟩)

def activeLocals (dst : LocalSlot) (src : LocalSlot := u8Arr2) : List LocalSlot :=
  [.init .unit, src, dst, .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
    .init (.ptr { allocId := 2, offsetBytes := 0 } 8)]

theorem k_copy_u8arr_to_maybeUninitBool :
    stepOutcome (copyActive tyU8A1 tyMUBool u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.unit, .scalar ⟨2, 1⟩]))) [] := rfl

theorem k_copy_u8arr_to_u8arr :
    stepOutcome (copyActive tyU8A1 tyU8A1 u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.scalar ⟨2, 1⟩]))) [] := rfl

theorem k_copy_maybeUninit_to_maybeUninit :
    stepOutcome (copyActive tyMUBool tyMUBool
      (.init (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]])) .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.unit, .scalar ⟨2, 1⟩]))
        (.init (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨2, 1⟩]]))) [] := rfl

/-- Premature write-time UB: an untyped `u8` copy into a `bool` local (conservative). -/
theorem k_copy_u8arr_to_bool_premature_ub :
    stepOutcome (copyActive tyU8A1 tyBool u8Arr2 .uninit) = .ub := rfl

theorem k_copy_u8_to_bool_premature_ub :
    stepOutcome (copyActive tyU8 tyBool u8Scalar2 .uninit) = .ub := rfl

/-- The copy into `Unaligned<bool>` stores an invalid `bool` field without any check. -/
theorem k_copy_u8arr_to_unalignedBool :
    stepOutcome (copyActive tyU8A1 tyUnalBool u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.scalar ⟨2, 1⟩]))) [] := rfl

theorem k_copy_u8arr_to_maybeUninitUnaligned :
    stepOutcome (copyActive tyU8A1 tyMUUnal u8Arr2 .uninit) =
      .step (activeLocals (.init (.aggregate 0 [.unit, .aggregate 0 [.scalar ⟨2, 1⟩]]))) [] := rfl

/-- Copy, then read place `_2` with projection `proj` from the resulting active frame. -/
def copyThenRead (srcTy dstTy : Ty) (srcSlot : LocalSlot) (proj : List ProjectionElem) :
    ReadOutcome :=
  match stepOutcome (copyActive srcTy dstTy srcSlot .uninit) with
  | .step locals _ =>
    readOutcome (evalOperand locals (.copy { local_ := 2, projection := proj }) [] [] kLayouts []
      [decl tyUnit, decl srcTy, decl dstTy, decl tyPtrU8, decl tyPtrU8] [])
  | _ => .unsupported

/-- **GAP (permissive, `Kani#5205`):** after the untyped copy of `2u8` into `Unaligned<bool>`,
reading field `.0 : bool` yields the invalid `bool` `2` without UB. -/
theorem k_gap_unalignedBool_field_reads_2 :
    copyThenRead tyU8A1 tyUnalBool u8Arr2 [.field 0 tyBool] = .ok (.scalar ⟨2, 1⟩) := rfl

/-- **GAP:** reading the whole `Unaligned<bool>` (a typed copy) also succeeds without UB. -/
theorem k_gap_unalignedBool_whole_reads_2 :
    copyThenRead tyU8A1 tyUnalBool u8Arr2 [] = .ok (.aggregate 0 [.scalar ⟨2, 1⟩]) := rfl

/-- **GAP:** `MaybeUninit<Unaligned<bool>>::assume_init` (field `.1`) yields an invalid
`Unaligned<bool>` without UB. -/
theorem k_gap_maybeUninitUnaligned_assume_init :
    copyThenRead tyU8A1 tyMUUnal u8Arr2 [.field 1 tyUnalBool] =
      .ok (.aggregate 0 [.scalar ⟨2, 1⟩]) := rfl

/-- Correct read-time UB: `MaybeUninit<bool>::assume_init` (field `.1 : bool`) on `2u8`. -/
theorem k_maybeUninitBool_assume_init_ub :
    copyThenRead tyU8A1 tyMUBool u8Arr2 [.field 1 tyBool] = .ub := rfl

theorem k_maybeUninitUnaligned_inner_field_ub :
    copyThenRead tyU8A1 tyMUUnal u8Arr2 [.field 1 tyUnalBool, .field 0 tyBool] = .ub := rfl

/-- Root `bool` locals are not re-validated on `Operand.copy`. -/
theorem k_bool_local_holding_2_reads_ok :
    readOutcome (evalOperand [.init .unit, .uninit, .init (.scalar ⟨2, 1⟩)] (.copy (lc 2)) [] []
      kLayouts [] [decl tyUnit, decl tyU8A1, decl tyBool] []) = .ok (.scalar ⟨2, 1⟩) := rfl

def wFnAbi : FnAbi :=
  { args := [], ret := { layout := tl 0 1 .memory (.arbitrary [] []) [], mode := .direct },
    conv := .rust, canUnwind := false }

def callerBody (dstTy : Ty) : CapturedMir :=
  { defPath := "caller", argCount := 0, localDecls := [decl tyUnit, decl dstTy],
    basicBlocks := [], phase := .runtimePostCleanup, role := .subject, fnAbi := wFnAbi,
    layouts := kLayouts, allocations := [] }

/-- Foreign-frame state: the destination `_1` lives in the caller frame (depth `0`). -/
def foreignState (srcSlot dstSlot : LocalSlot) (dstTy : Ty) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init .unit, srcSlot, .uninit,
      .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 2, offsetBytes := 0 } 8)] },
    memory := { emptyMemory with
      borrows := [
        { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique,
          targetFrameDepth := 1 },
        { tag := 2, targetLocal := 1, targetProjection := [], perm := .unique,
          targetFrameDepth := 0 }],
      nextTag := 3,
      callStack := [
        { callerBody := callerBody dstTy,
          frame := { blockIdx := 0, stmtIdx := 0, locals := [.init .unit, dstSlot] },
          destination := lc 0 }] } }

def copyForeign (srcTy dstTy : Ty) (srcSlot dstSlot : LocalSlot) : MirStepNode :=
  evalCopyNonOverlapping (foreignState srcSlot dstSlot dstTy) (.copy (lc 3)) (.copy (lc 4))
    (usz 1) [decl tyUnit, decl srcTy, decl tyUnit, decl tyPtrU8, decl tyPtrU8] kLayouts

def foreignActive (src : LocalSlot) : List LocalSlot :=
  [.init .unit, src, .uninit, .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
    .init (.ptr { allocId := 2, offsetBytes := 0 } 8)]

/-- **GAP (permissive):** a foreign-frame `copy_nonoverlapping` of `2u8` into the caller's
`bool` local stores `2` with no check (the active-frame path reports premature UB). -/
theorem k_gap_foreign_u8_to_bool_stores_2 :
    stepOutcome (copyForeign tyU8 tyBool u8Scalar2 .uninit) =
      .step (foreignActive u8Scalar2) [[.init .unit, .init (.scalar ⟨2, 1⟩)]] := rfl

/-- Foreign-frame copy of a `[u8; 1]` value into a caller `bool` stores an array value. -/
theorem k_gap_foreign_u8arr_to_bool_stores_array :
    stepOutcome (copyForeign tyU8A1 tyBool u8Arr2 .uninit) =
      .step (foreignActive u8Arr2) [[.init .unit, .init (.aggregate 0 [.scalar ⟨2, 1⟩])]] := rfl

/-- Foreign-frame copy into a caller `MaybeUninit<bool>` stores the raw source value. -/
theorem k_foreign_u8_to_maybeUninitBool :
    stepOutcome (copyForeign tyU8 tyMUBool u8Scalar2 .uninit) =
      .step (foreignActive u8Scalar2) [[.init .unit, .init (.scalar ⟨2, 1⟩)]] := rfl

/-! Parity gap: `V2026_08_01` defines no `writeBytesAction` / `write_bytes`
model (the intrinsic is not interpreted by this snapshot), so the `write_bytes`
audit applies to `V2026_06_01` only. -/

/-! ### Prototype on the same inputs: stripped where live retains -/

/-- The prototype bytes project exactly onto the live encoder's bytes. -/
theorem proto_projects_to_liveEnc :
    (encodePtrBytesProto ⟨1, 1, 0x1122334455667788⟩ 8).map AbstractByteProto.toLive08 =
      liveEnc 1 1 0x1122334455667788 8 := rfl

end LiveV08

/-! ## 12. Concrete 3-way witnesses: prototype vs live MiniRust vs Miri mirror -/

/-- Live MiniRust `encode_ptr` bytes of a 64-bit pointer into allocation `a`. -/
def mrEnc (a off : Nat) : List MiniRustSpec.Interp.Byte :=
  MiniRustSpec.Interp.encodePtrBytes (some (mrProv a)) 0 (leImage off 8)

/-- Live MiniRust `encode_ptr` bytes of a 32-bit pointer image (decoded with the provenance
fold, since the vendored `x86_64` target fixes `PTR_SIZE = 8`). -/
def mrEnc4 (a off : Nat) : List MiniRustSpec.Interp.Byte :=
  MiniRustSpec.Interp.encodePtrBytes (some (mrProv a)) 0 (leImage off 4)

theorem mr_intact :
    MiniRustSpec.Interp.decodePtr (mrEnc 1 0x1122) =
      .ok (some { addr := 0x1122, provenance := some (mrProv 1) }) := rfl

theorem mr_w1_rev8 :
    MiniRustSpec.Interp.decodePtr (mrEnc 1 0x1122334455667788).reverse =
      .ok (some { addr := 0x8877665544332211, provenance := none }) := rfl

theorem mr_w1_rev8_zero :
    MiniRustSpec.Interp.decodePtr (mrEnc 1 0).reverse =
      .ok (some { addr := 0, provenance := none }) := rfl

theorem mr_w1_rev4 : mrDecodedProv (mrEnc4 1 0x11223344).reverse = none := rfl

theorem mr_w1_swap01 :
    MiniRustSpec.Interp.decodePtr (swapFirstTwo (mrEnc 1 0x1122)) =
      .ok (some { addr := 0x2211, provenance := none }) := rfl

theorem mr_w1_dup0 :
    MiniRustSpec.Interp.decodePtr (dupFirstByte (mrEnc 1 0x1122)) =
      .ok (some { addr := 0x2222222222222222, provenance := none }) := rfl

/-- **MiniRust keeps provenance on same-allocation offset splices (`UCG#558`).** -/
theorem mr_w2_splice_0_256 :
    MiniRustSpec.Interp.decodePtr (spliceBytes 1 (mrEnc 1 0) (mrEnc 1 256)) =
      .ok (some { addr := 256, provenance := some (mrProv 1) }) := rfl

theorem mr_w2_splice_0_4 :
    MiniRustSpec.Interp.decodePtr (spliceBytes 1 (mrEnc 1 0) (mrEnc 1 4)) =
      .ok (some { addr := 0, provenance := some (mrProv 1) }) := rfl

theorem mr_w2_splice_10_14 :
    MiniRustSpec.Interp.decodePtr (spliceBytes 1 (mrEnc 1 0x10) (mrEnc 1 0x14)) =
      .ok (some { addr := 0x10, provenance := some (mrProv 1) }) := rfl

/-- Miri-mirror fragments of a prototype byte list. -/
def miriFrags (l : List AbstractByteProto) : List (Option (PointerFragMirror (Nat × Nat))) :=
  l.map toMiriFrag

theorem miri_intact :
    inspectFragmentsMirror none (miriFrags (encodePtrBytesProto ⟨1, 1, 0x1122⟩ 8)) =
      .ok (some (1, 1)) := rfl

theorem miri_w1_rev8 :
    inspectFragmentsMirror none
      (miriFrags (encodePtrBytesProto ⟨1, 1, 0x1122334455667788⟩ 8).reverse) = .ok none := rfl

theorem miri_w1_rev8_zero :
    inspectFragmentsMirror none (miriFrags (encodePtrBytesProto ⟨1, 1, 0⟩ 8).reverse) =
      .ok none := rfl

theorem miri_w1_rev4 :
    inspectFragmentsMirror none (miriFrags (encodePtrBytesProto ⟨1, 1, 0x11223344⟩ 4).reverse) =
      .ok none := rfl

theorem miri_w1_swap01 :
    inspectFragmentsMirror none (miriFrags (swapFirstTwo (encodePtrBytesProto ⟨1, 1, 0x1122⟩ 8))) =
      .ok none := rfl

theorem miri_w1_dup0 :
    inspectFragmentsMirror none (miriFrags (dupFirstByte (encodePtrBytesProto ⟨1, 1, 0x1122⟩ 8))) =
      .ok none := rfl

theorem miri_w2_splice_0_256 :
    inspectFragmentsMirror none (miriFrags
      (spliceBytes 1 (encodePtrBytesProto ⟨1, 1, 0⟩ 8) (encodePtrBytesProto ⟨1, 1, 256⟩ 8))) =
      .ok none := rfl

theorem miri_w2_splice_0_4 :
    inspectFragmentsMirror none (miriFrags
      (spliceBytes 1 (encodePtrBytesProto ⟨1, 1, 0⟩ 8) (encodePtrBytesProto ⟨1, 1, 4⟩ 8))) =
      .ok none := rfl

theorem miri_w2_splice_10_14 :
    inspectFragmentsMirror none (miriFrags
      (spliceBytes 1 (encodePtrBytesProto ⟨1, 1, 0x10⟩ 8) (encodePtrBytesProto ⟨1, 1, 0x14⟩ 8))) =
      .ok none := rfl

/-- Mirror fidelity: wildcard fragments are skipped (`continue`) and an all-wildcard image
returns the wildcard; with no wildcard and no fragments, `missingWildcard` is thrown. -/
theorem miri_wildcard_semantics :
    inspectFragmentsMirror (some (0, 0))
      [some ⟨0, (0, 0), imageVec8 0⟩, some ⟨1, (1, 1), imageVec8 0x1122⟩] = .ok (some (1, 1)) ∧
    inspectFragmentsMirror (some (0, 0)) [some ⟨5, (0, 0), imageVec8 0⟩] = .ok (some (0, 0)) ∧
    inspectFragmentsMirror (none : Option (Nat × Nat)) [] = .missingWildcard := ⟨rfl, rfl, rfl⟩

/-- Mirror fidelity: `frag.idx.toNat != idx` and `(frag.prov, frag.bytes) != pair` both
return `none`; a missing fragment returns `none`. -/
theorem miri_mismatch_semantics :
    inspectFragmentsMirror none [some ⟨1, (1, 1), imageVec8 0⟩] = .ok none ∧
    inspectFragmentsMirror none
      [some ⟨0, (1, 1), imageVec8 0⟩, some ⟨1, (1, 1), imageVec8 1⟩] = .ok none ∧
    inspectFragmentsMirror none
      [some ⟨0, (1, 1), imageVec8 0⟩, some ⟨1, (1, 2), imageVec8 0⟩] = .ok none ∧
    inspectFragmentsMirror none [some ⟨0, (1, 1), imageVec8 0⟩, none] = .ok none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **W2 five-way summary:** on the same-`(allocId, tag)` `p = 0` / `p + 256` splice, live
`V2026_06_01` and `V2026_08_01` and live MiniRust keep provenance, while Miri and the
prototype strip it. -/
theorem w2_five_way :
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
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **W1 five-way summary (all-zero pointer, byte-reversed):** both live snapshots keep
provenance; MiniRust, Miri and the prototype strip it. -/
theorem w1_five_way_zero_rev :
    LiveV06.decodePtrBytesNoForgeLive true 8 (LiveV06.liveEnc 1 1 0 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0 } 8) ∧
    LiveV08.decodePtrBytesNoForgeLive true 8 (LiveV08.liveEnc 1 1 0 8).reverse =
      some (.ptr { allocId := 1, offsetBytes := 0 } 8) ∧
    MiniRustSpec.Interp.decodePtr (mrEnc 1 0).reverse =
      .ok (some { addr := 0, provenance := none }) ∧
    inspectFragmentsMirror none (miriFrags (encodePtrBytesProto ⟨1, 1, 0⟩ 8).reverse) = .ok none ∧
    decodePtrBytesNoForgeProto true .thin 8 (encodePtrBytesProto ⟨1, 1, 0⟩ 8).reverse = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Anneal.Proto.Ucg558PtrByteCoherenceProto
