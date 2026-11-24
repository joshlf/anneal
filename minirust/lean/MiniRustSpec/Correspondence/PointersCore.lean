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
# Raw pointers and references: representation and aliasing analysis (MR-3.1, MR-3.2)

First of the four modules that make up `MiniRustSpec.Correspondence.Pointers` (see its module
documentation for the overall statement; the split keeps every declaration, name, and proof
unchanged and only bounds the memory needed to elaborate one module):

* MiniRust's representation of thin pointers and safe references (`encode_ptr`, `decode_ptr`,
  `check_value` at `PtrType::Raw` / `PtrType::Ref`);
* Anneal's model of raw pointers and references as Tree Borrows tags (`evalRvalue_rawPtr_local`,
  `evalRvalue_ref_local`, reborrows, `Offset`, `PtrToPtr`, `PointerExposeProvenance`);
* MiniRust's `ReborrowSettings::new` / `Statement::Validate`, thin-pointer loads, stores, and
  zero-offset arithmetic;
* Anneal's Tree Borrows preservation under the flow-sensitive static analysis `ptrAliasingOk`,
  and the first consequences of `ptrAliasingOk` (`BorrowsOk`, `ptrEnvBefore`).

`PointersLattice` continues with the `PtrLocalState` join-semilattice and fixed-point theory.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open Trusted.Sequence

/-! ## MiniRust: the representation of thin pointers -/

theorem encodePtrBytes_data (prov : Option Prov) (i : Nat) (data : List UInt8) :
    (encodePtrBytes prov i data).mapM AbstractByte.data = some data := by
  induction data generalizing i with
  | nil => rfl
  | cons b rest ih => simp [encodePtrBytes, AbstractByte.data, ih]

/-- The provenance fold of `decode_ptr` keeps a provenance whose fragments sit
at their own positions. -/
theorem decodePtrProvenance_encode (prov : Option Prov) (i : Nat) (data : List UInt8) :
    decodePtrProvenance i prov (encodePtrBytes prov i data) = prov := by
  induction data generalizing i with
  | nil => rfl
  | cons b rest ih =>
    cases prov with
    | none => simp [encodePtrBytes, decodePtrProvenance, AbstractByte.provenance_frag, ih]
    | some p => simp [encodePtrBytes, decodePtrProvenance, AbstractByte.provenance_frag, ih]

/-- Once the provenance fold of `decode_ptr` has lost the provenance, it stays
lost ("Crucially, if `acc` is ever `None`, it remains `None`"). -/
theorem decodePtrProvenance_none (i : Nat) (bytes : List Byte) :
    decodePtrProvenance i none bytes = none := by
  induction bytes generalizing i with
  | nil => rfl
  | cons b rest ih =>
    simp only [decodePtrProvenance]
    split <;> simp_all

/-- `2^64`, the size of the address space of `x86_64`, as an integer literal. -/
theorem two_pow_ptrBits : (2 : Int) ^ Size.bits x86_64.PTR_SIZE = 18446744073709551616 := by
  decide

/-- `Int::in_bounds(Unsigned, PTR_SIZE)` with the bound as a literal. -/
theorem inBounds_usize (i : Int) :
    inBounds i .Unsigned x86_64.PTR_SIZE = (decide (0 ≤ i) && decide (i < 18446744073709551616)) := by
  simp only [inBounds, two_pow_ptrBits]

theorem lt_two_pow_64_int {addr : Nat} (h : addr < 2 ^ 64) : (addr : Int) < 18446744073709551616 := by
  have : addr < 18446744073709551616 := by simpa using h
  omega

/-- `Endianness::encode(Unsigned, PTR_SIZE, addr)` for an address in
`[0, 2^64)`: its eight little-endian bytes. -/
theorem encode_usize (addr : Nat) (h : addr < 2 ^ 64) :
    Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE (addr : Int) =
      some (leBytes addr 8) := by
  have hlt := lt_two_pow_64_int h
  have hin : inBounds (addr : Int) .Unsigned x86_64.PTR_SIZE = true := by
    rw [inBounds_usize]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  have hmod : ((addr : Int) % (2 : Int) ^ Size.bits x86_64.PTR_SIZE).toNat = addr := by
    rw [two_pow_ptrBits, Int.emod_eq_of_lt (by omega) hlt]; simp
  unfold Endianness.encode
  simp only [hin, ↓reduceIte, hmod]
  rfl

theorem encodePtr_of_encode (ptr : Ptr) (data : List UInt8)
    (henc : Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE ptr.addr = some data) :
    encodePtr ptr = .ok (encodePtrBytes ptr.provenance 0 data) := by
  unfold encodePtr
  rw [henc]
  rfl

theorem encodePtr_eq (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) :
    encodePtr { addr := addr, provenance := prov } = .ok (ptrBytes addr prov) :=
  encodePtr_of_encode { addr := addr, provenance := prov } (leBytes addr 8) (encode_usize addr h)

theorem firstProvenance_encodePtrBytes (prov : Option Prov) (b : UInt8) (rest : List UInt8) :
    firstProvenance (encodePtrBytes prov 0 (b :: rest)) = prov := by
  cases prov <;> simp [encodePtrBytes, firstProvenance, AbstractByte.provenance_frag]

theorem decodePtr_ptrBytes (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) :
    decodePtr (ptrBytes addr prov) = .ok (some { addr := addr, provenance := prov }) := by
  have hdata := encodePtrBytes_data prov 0 (leBytes addr 8)
  have h256 : addr < 256 ^ 8 := by
    have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [this]; exact h
  have hval : Endianness.decode x86_64.ENDIANNESS .Unsigned (leBytes addr 8) = (addr : Int) := by
    simp only [Endianness.decode, x86_64.ENDIANNESS, leValue_leBytes, Nat.mod_eq_of_lt h256]
  have hlen : (ptrBytes addr prov).length = x86_64.PTR_SIZE.bytes := ptrBytes_length addr prov
  have hfirst : firstProvenance (ptrBytes addr prov) = prov := by
    have hcons : leBytes addr 8 = UInt8.ofNat (addr % 256) :: leBytes (addr / 256) 7 := rfl
    unfold ptrBytes; rw [hcons]; exact firstProvenance_encodePtrBytes prov _ _
  unfold decodePtr
  simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hfirst]
  unfold ptrBytes
  rw [hdata]
  simp only [hval, decodePtrProvenance_encode]
  rfl

/-- Two fragments of *different* provenances: the provenance fold of
`decode_ptr` loses the provenance as soon as a byte's fragment does not match
the first byte's. -/
theorem decodePtrProvenance_mixed (i : Nat) (p q : Prov) (hpq : p ≠ q) (b : UInt8)
    (rest : List Byte) :
    decodePtrProvenance i (some p) (.Init b (some ⟨q, (i : Int)⟩) :: rest) = none := by
  simp [decodePtrProvenance, AbstractByte.provenance_frag, Ne.symm hpq,
    decodePtrProvenance_none]

theorem layout_thinRawPtr : Type.layout thinRawPtrTy = .ok (.Sized ⟨8⟩ ⟨8⟩) := rfl

theorem decode_thinRawPtr (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) :
    Type.decode thinRawPtrTy (ptrBytes addr prov) =
      .ok (some (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })) := by
  simp only [thinRawPtrTy, Type.decode, PtrType.as_wide_pair, PtrType.meta_kind]
  rw [decodePtr_ptrBytes addr h prov]
  rfl

theorem encode_thinRawPtr (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) :
    Type.encode thinRawPtrTy
        (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none }) =
      .ok (ptrBytes addr prov) := by
  simp only [thinRawPtrTy, Type.encode, PtrType.as_wide_pair, PtrType.meta_kind]
  exact encodePtr_eq addr h prov

theorem checkValue_thinRawPtr {m? : Option Mach} (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) :
    checkValue (m := m?) (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })
      thinRawPtrTy = .ok () := by
  have hlt := lt_two_pow_64_int h
  have hin : inBounds (addr : Int) .Unsigned x86_64.PTR_SIZE = true := by
    rw [inBounds_usize]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  simp [thinRawPtrTy, checkValue, checkPtr, hin, ensureElseUb, checkPtrMetadata,
    PtrType.meta_kind, PtrType.safe_pointee]

/-- An address outside `[0, 2^64)` is not a valid raw pointer
(`Value::Ptr: pointer out-of-bounds`). -/
theorem checkValue_thinRawPtr_oob {m? : Option Mach} (addr : Int)
    (h : ¬ (0 ≤ addr ∧ addr < 18446744073709551616)) (prov : Option Prov) :
    checkValue (m := m?) (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })
      thinRawPtrTy = .error (.ub "Value::Ptr: pointer out-of-bounds") := by
  have hin : inBounds addr .Unsigned x86_64.PTR_SIZE = false := by
    rw [inBounds_usize]
    by_cases h0 : 0 ≤ addr
    · have : ¬ addr < 18446744073709551616 := fun h' => h ⟨h0, h'⟩
      simp [h0, this]
    · simp [h0]
  simp [thinRawPtrTy, checkValue, checkPtr, hin, ensureElseUb, ub]

theorem layout_refTy (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType) :
    Type.layout (refTy mutbl pointeeIt) = .ok (.Sized ⟨8⟩ ⟨8⟩) := rfl

theorem decode_refTy (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) :
    Type.decode (refTy mutbl pointeeIt) (ptrBytes addr prov) =
      .ok (some (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })) := by
  simp only [refTy, refPtrType, intPointeeInfo, Type.decode, PtrType.as_wide_pair, PtrType.meta_kind]
  rw [decodePtr_ptrBytes addr h prov]
  rfl

theorem decode_refTy_uninit (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType) :
    Type.decode (refTy mutbl pointeeIt) (uninitBytes usizeIt) = .ok none := rfl

theorem encode_refTy (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) :
    Type.encode (refTy mutbl pointeeIt)
        (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none }) =
      .ok (ptrBytes addr prov) := by
  simp only [refTy, refPtrType, intPointeeInfo, Type.encode, PtrType.as_wide_pair, PtrType.meta_kind]
  exact encodePtr_eq addr h prov

theorem inBounds_goodSize {sz : Size} (hgood : GoodSize sz.bytes) :
    inBounds (sz.bytes : Int) .Signed x86_64.PTR_SIZE = true := by
  rcases hgood with h1 | h2 | h4 | h8 | h16
  · rw [h1]; decide
  · rw [h2]; decide
  · rw [h4]; decide
  · rw [h8]; decide
  · rw [h16]; decide

/-- The metadata check of a thin pointer (`(None, PointerMetaKind::None) => {}`)
passes whatever the machine argument is. The machine is an explicit argument
without a default value, so that `rw [checkPtrMetadata_none]` rewrites
`checkPtrMetadata none .None m` for every `m`. -/
@[simp] theorem checkPtrMetadata_none (m : Option Mach) :
    checkPtrMetadata none .None m = .ok () := rfl

@[simp] theorem compute_size_and_align_sized {Provenance : Type}
    (vtables : Gen.ThinPointer Provenance → Interp Gen.VTable) (sz : Size) (al : Align) :
    LayoutStrategy.compute_size_and_align vtables (.Sized sz al) none = .ok (sz, al) := rfl

theorem checkValue_refTy (m : Mach) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (hgood : GoodSize pointeeIt.size.bytes)
    (addr : Nat) (hpos : 0 < addr) (hlt : addr < 2 ^ 64) (prov : Option Prov)
    (hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (addr : Int) = true)
    (hderef : CM.dereferenceable m.mem { addr := (addr : Int), provenance := prov } pointeeIt.size = .ok ()) :
    checkValue (m := some m)
      (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })
      (refTy mutbl pointeeIt) = .ok () := by
  have hlt' := lt_two_pow_64_int hlt
  have hin : inBounds (addr : Int) .Unsigned x86_64.PTR_SIZE = true := by
    rw [inBounds_usize]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  have hnz : ((addr : Int) != 0) = true := by simp [bne_iff_ne]; omega
  have hsz : inBounds (pointeeIt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true :=
    inBounds_goodSize hgood
  unfold checkValue refTy checkPtr refPtrType intPointeeInfo
  dsimp only [PtrType.meta_kind, LayoutStrategy.meta_kind, PtrType.safe_pointee]
  rw [hin, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
    compute_size_and_align_sized, ok_bind, hsz, ensureElseUb_true, ok_bind,
    hnz, ensureElseUb_true, ok_bind, hal, ensureElseUb_true, ok_bind,
    ensureElseUb_true, ok_bind, hderef]
  rfl

/-- A null address (`0`) is rejected by `checkValue` at every safe reference type
(`Value::Ptr: null safe pointer`). -/
theorem checkValue_refTy_null_ub (m? : Option Mach) (mutbl : MirAst.Mutability)
    (pointeeIt : Gen.IntType) (hgood : GoodSize pointeeIt.size.bytes) (prov : Option Prov) :
    checkValue (m := m?)
      (.Ptr { thin_pointer := { addr := 0, provenance := prov }, metadata := none })
      (refTy mutbl pointeeIt) = .error (.ub "Value::Ptr: null safe pointer") := by
  have hin : inBounds (0 : Int) .Unsigned x86_64.PTR_SIZE = true := by
    rw [inBounds_usize]; simp
  have hnz : ((0 : Int) != 0) = false := rfl
  have hsz : inBounds (pointeeIt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true :=
    inBounds_goodSize hgood
  unfold checkValue refTy checkPtr refPtrType intPointeeInfo
  dsimp only [PtrType.meta_kind, LayoutStrategy.meta_kind, PtrType.safe_pointee]
  rw [hin, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
    compute_size_and_align_sized, ok_bind, hsz, ensureElseUb_true, ok_bind,
    hnz, ensureElseUb_false, error_bind]

/-- A non-zero address that is not aligned to the pointee's alignment is rejected
by `checkValue` at every safe reference type (`Value::Ptr: unaligned safe pointer`). -/
theorem checkValue_refTy_unaligned_ub (m? : Option Mach) (mutbl : MirAst.Mutability)
    (pointeeIt : Gen.IntType) (hgood : GoodSize pointeeIt.size.bytes)
    (addr : Nat) (hpos : 0 < addr) (hlt : addr < 2 ^ 64)
    (prov : Option Prov)
    (hunal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (addr : Int) = false) :
    checkValue (m := m?)
      (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })
      (refTy mutbl pointeeIt) = .error (.ub "Value::Ptr: unaligned safe pointer") := by
  have hlt' := lt_two_pow_64_int hlt
  have hin : inBounds (addr : Int) .Unsigned x86_64.PTR_SIZE = true := by
    rw [inBounds_usize]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  have hnz : ((addr : Int) != 0) = true := by simp [bne_iff_ne]; omega
  have hsz : inBounds (pointeeIt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true :=
    inBounds_goodSize hgood
  unfold checkValue refTy checkPtr refPtrType intPointeeInfo
  dsimp only [PtrType.meta_kind, LayoutStrategy.meta_kind, PtrType.safe_pointee]
  rw [hin, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
    compute_size_and_align_sized, ok_bind, hsz, ensureElseUb_true, ok_bind,
    hnz, ensureElseUb_true, ok_bind, hunal, ensureElseUb_false, error_bind]

/-- A non-null, aligned safe reference that is not dereferenceable in `m.mem`
(no provenance, dead allocation, or out-of-bounds range) is rejected by
`checkValue` with `"Value::Ptr: non-dereferenceable safe pointer"`. -/
theorem checkValue_refTy_dangling_ub (m : Mach) (mutbl : MirAst.Mutability)
    (pointeeIt : Gen.IntType) (hgood : GoodSize pointeeIt.size.bytes)
    (addr : Nat) (hpos : 0 < addr) (hlt : addr < 2 ^ 64) (prov : Option Prov)
    (hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (addr : Int) = true)
    (msg : String)
    (hderef : CM.dereferenceable m.mem { addr := (addr : Int), provenance := prov } pointeeIt.size =
      .error (.ub msg)) :
    checkValue (m := some m)
      (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })
      (refTy mutbl pointeeIt) = .error (.ub "Value::Ptr: non-dereferenceable safe pointer") := by
  have hlt' := lt_two_pow_64_int hlt
  have hin : inBounds (addr : Int) .Unsigned x86_64.PTR_SIZE = true := by
    rw [inBounds_usize]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  have hnz : ((addr : Int) != 0) = true := by simp [bne_iff_ne]; omega
  have hsz : inBounds (pointeeIt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true :=
    inBounds_goodSize hgood
  unfold checkValue refTy checkPtr refPtrType intPointeeInfo
  dsimp only [PtrType.meta_kind, LayoutStrategy.meta_kind, PtrType.safe_pointee]
  rw [hin, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
    compute_size_and_align_sized, ok_bind, hsz, ensureElseUb_true, ok_bind,
    hnz, ensureElseUb_true, ok_bind, hal, ensureElseUb_true, ok_bind,
    ensureElseUb_true, ok_bind, hderef]
  rfl

theorem layout_declPtrTy (t : MirAst.Ty) :
    Type.layout (declPtrTy t) = .ok (.Sized ⟨8⟩ ⟨8⟩) := by
  rcases declPtrTy_cases t with h | ⟨_, _, _, h⟩ <;> rw [h] <;> rfl

theorem decode_declPtrTy (t : MirAst.Ty) (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) :
    Type.decode (declPtrTy t) (ptrBytes addr prov) =
      .ok (some (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })) := by
  rcases declPtrTy_cases t with hty | ⟨mutbl, it, _, hty⟩
  · rw [hty]; exact decode_thinRawPtr addr h prov
  · rw [hty]; exact decode_refTy mutbl it addr h prov

theorem decode_declPtrTy_uninit (t : MirAst.Ty) :
    Type.decode (declPtrTy t) (uninitBytes usizeIt) = .ok none := by
  rcases declPtrTy_cases t with hty | ⟨_, _, _, hty⟩ <;> rw [hty] <;> rfl

theorem encode_declPtrTy (t : MirAst.Ty) (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) :
    Type.encode (declPtrTy t)
        (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none }) =
      .ok (ptrBytes addr prov) := by
  rcases declPtrTy_cases t with hty | ⟨mutbl, it, _, hty⟩
  · rw [hty]; exact encode_thinRawPtr addr h prov
  · rw [hty]; exact encode_refTy mutbl it addr h prov

theorem checkValue_declPtrTy {t : MirAst.Ty} {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType}
    (hp : ptrPointeeOf t = some (mutbl, pointeeIt))
    (m : Mach) (hgood : GoodSize pointeeIt.size.bytes)
    (addr : Nat) (hpos : 0 < addr) (hlt : addr < 2 ^ 64) (prov : Option Prov)
    (hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (addr : Int) = true)
    (hderef : CM.dereferenceable m.mem { addr := (addr : Int), provenance := prov } pointeeIt.size = .ok ()) :
    checkValue (m := some m)
      (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })
      (declPtrTy t) = .ok () := by
  rcases declPtrTy_cases t with hty | ⟨m', it', href, hty⟩
  · rw [hty]; exact checkValue_thinRawPtr addr hlt prov
  · obtain ⟨hp', _⟩ := ptrPointeeOf_of_refPointeeOf href
    rw [hp] at hp'; simp only [Option.some.injEq, Prod.mk.injEq] at hp'
    obtain ⟨rfl, rfl⟩ := hp'
    rw [hty]; exact checkValue_refTy m mutbl pointeeIt hgood addr hpos hlt prov hal hderef

private theorem size_ne_self_ite {α : Type} (s : Size) (t e : α) :
    (if s ≠ s then t else e) = e := by
  split
  · next h => exact absurd rfl h
  · rfl

theorem transmute_refTy_ok (m : Mach) (mutbl : MirAst.Mutability)
    (pointeeIt : Gen.IntType) (hgood : GoodSize pointeeIt.size.bytes)
    (addr : Nat) (hpos : 0 < addr) (hlt : addr < 2 ^ 64) (prov : Option Prov)
    (hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (addr : Int) = true)
    (hderef : CM.dereferenceable m.mem { addr := (addr : Int), provenance := prov } pointeeIt.size = .ok ()) :
    transmute
      (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })
      thinRawPtrTy (refTy mutbl pointeeIt) (some m) =
    .ok (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none }) := by
  unfold transmute
  rw [layout_thinRawPtr, ok_bind, expect_size_sized, ok_bind,
    layout_refTy mutbl pointeeIt, ok_bind, expect_size_sized, ok_bind,
    size_ne_self_ite,
    encode_thinRawPtr addr hlt prov, ok_bind,
    decode_refTy mutbl pointeeIt addr hlt prov, ok_bind]
  dsimp only []
  rw [checkValue_refTy m mutbl pointeeIt hgood addr hpos hlt prov hal hderef, ok_bind]
  rfl

theorem transmute_refTy_dangling_ub (m : Mach) (mutbl : MirAst.Mutability)
    (pointeeIt : Gen.IntType) (hgood : GoodSize pointeeIt.size.bytes)
    (addr : Nat) (hpos : 0 < addr) (hlt : addr < 2 ^ 64) (prov : Option Prov)
    (hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (addr : Int) = true)
    (msg : String)
    (hderef : CM.dereferenceable m.mem { addr := (addr : Int), provenance := prov } pointeeIt.size =
      .error (.ub msg)) :
    transmute
      (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })
      thinRawPtrTy (refTy mutbl pointeeIt) (some m) =
    .error (.ub "Value::Ptr: non-dereferenceable safe pointer") := by
  unfold transmute
  rw [layout_thinRawPtr, ok_bind, expect_size_sized, ok_bind,
    layout_refTy mutbl pointeeIt, ok_bind, expect_size_sized, ok_bind,
    size_ne_self_ite,
    encode_thinRawPtr addr hlt prov, ok_bind,
    decode_refTy mutbl pointeeIt addr hlt prov, ok_bind]
  dsimp only []
  rw [checkValue_refTy_dangling_ub m mutbl pointeeIt hgood addr hpos hlt prov hal msg hderef]
  rfl

/-- Transmuting a thin raw pointer to a safe reference type `refTy mutbl pointeeIt`
on machine `some m` succeeds when the pointer is non-null, aligned to
`pointeeIt`, and dereferenceable in `m.mem`. -/
theorem evalCastOp_transmute_refTy_ok (m : Mach) (mutbl : MirAst.Mutability)
    (pointeeIt : Gen.IntType) (hgood : GoodSize pointeeIt.size.bytes)
    (addr : Nat) (hpos : 0 < addr) (hlt : addr < 2 ^ 64) (prov : Option Prov)
    (hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (addr : Int) = true)
    (hderef : CM.dereferenceable m.mem { addr := (addr : Int), provenance := prov } pointeeIt.size = .ok ()) :
    evalCastOp (.Transmute (refTy mutbl pointeeIt))
      (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none }, thinRawPtrTy)
      (some m) =
    .ok (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none },
         refTy mutbl pointeeIt) := by
  unfold evalCastOp
  dsimp only []
  rw [layout_thinRawPtr, ok_bind, expect_size_sized, ok_bind,
    layout_refTy mutbl pointeeIt, ok_bind, expect_size_sized, ok_bind,
    size_ne_self_ite,
    transmute_refTy_ok m mutbl pointeeIt hgood addr hpos hlt prov hal hderef, ok_bind]
  rfl

/-- Transmuting a thin raw pointer to a safe reference type `refTy mutbl pointeeIt`
on machine `some m` raises `"Value::Ptr: non-dereferenceable safe pointer"` when
`m.mem` rejects `dereferenceable` (e.g. dead stack allocation, out-of-bounds
offset, or missing provenance). -/
theorem evalCastOp_transmute_refTy_dangling_ub (m : Mach) (mutbl : MirAst.Mutability)
    (pointeeIt : Gen.IntType) (hgood : GoodSize pointeeIt.size.bytes)
    (addr : Nat) (hpos : 0 < addr) (hlt : addr < 2 ^ 64) (prov : Option Prov)
    (hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (addr : Int) = true)
    (msg : String)
    (hderef : CM.dereferenceable m.mem { addr := (addr : Int), provenance := prov } pointeeIt.size =
      .error (.ub msg)) :
    evalCastOp (.Transmute (refTy mutbl pointeeIt))
      (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none }, thinRawPtrTy)
      (some m) =
    .error (.ub "Value::Ptr: non-dereferenceable safe pointer") := by
  unfold evalCastOp
  dsimp only []
  rw [layout_thinRawPtr, ok_bind, expect_size_sized, ok_bind,
    layout_refTy mutbl pointeeIt, ok_bind, expect_size_sized, ok_bind,
    size_ne_self_ite,
    transmute_refTy_dangling_ub m mutbl pointeeIt hgood addr hpos hlt prov hal msg hderef]
  rfl

/-- Transmuting between any two thin pointer or reference types (`declPtrTy srcTy`
to `declPtrTy dstTy`) on machine `some m` succeeds when the pointer is non-null,
aligned to `pointeeIt`, and dereferenceable in `m.mem`. -/
theorem transmute_declPtrTy_ok (m : Mach) (srcTy dstTy : MirAst.Ty)
    {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType}
    (hp : ptrPointeeOf dstTy = some (mutbl, pointeeIt))
    (hgood : GoodSize pointeeIt.size.bytes)
    (addr : Nat) (hpos : 0 < addr) (hlt : addr < 2 ^ 64) (prov : Option Prov)
    (hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (addr : Int) = true)
    (hderef : CM.dereferenceable m.mem { addr := (addr : Int), provenance := prov } pointeeIt.size = .ok ()) :
    transmute
      (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })
      (declPtrTy srcTy) (declPtrTy dstTy) (some m) =
    .ok (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none }) := by
  unfold transmute
  rw [layout_declPtrTy srcTy, ok_bind, expect_size_sized, ok_bind,
    layout_declPtrTy dstTy, ok_bind, expect_size_sized, ok_bind,
    size_ne_self_ite,
    encode_declPtrTy srcTy addr hlt prov, ok_bind,
    decode_declPtrTy dstTy addr hlt prov, ok_bind]
  dsimp only []
  rw [checkValue_declPtrTy hp m hgood addr hpos hlt prov hal hderef, ok_bind]
  rfl

/-- `evalCastOp (.Transmute (declPtrTy dstTy))` between any two thin pointer or
reference types (`declPtrTy srcTy` to `declPtrTy dstTy`) on machine `some m`
succeeds and preserves the pointer value when non-null, aligned, and
dereferenceable in `m.mem`. -/
theorem evalCastOp_transmute_declPtrTy_ok (m : Mach) (srcTy dstTy : MirAst.Ty)
    {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType}
    (hp : ptrPointeeOf dstTy = some (mutbl, pointeeIt))
    (hgood : GoodSize pointeeIt.size.bytes)
    (addr : Nat) (hpos : 0 < addr) (hlt : addr < 2 ^ 64) (prov : Option Prov)
    (hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (addr : Int) = true)
    (hderef : CM.dereferenceable m.mem { addr := (addr : Int), provenance := prov } pointeeIt.size = .ok ()) :
    evalCastOp (.Transmute (declPtrTy dstTy))
      (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none },
       declPtrTy srcTy)
      (some m) =
    .ok (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none },
         declPtrTy dstTy) := by
  unfold evalCastOp
  dsimp only []
  rw [layout_declPtrTy srcTy, ok_bind, expect_size_sized, ok_bind,
    layout_declPtrTy dstTy, ok_bind, expect_size_sized, ok_bind,
    size_ne_self_ite,
    transmute_declPtrTy_ok m srcTy dstTy hp hgood addr hpos hlt prov hal hderef, ok_bind]
  rfl

/-! ## Anneal: raw pointers as Tree Borrows tags -/

/-- A projection without `Index` or `Subslice`, which Anneal's `&raw` stores as it is
(`resolveBorrowProjectionElems` rewrites only `Index` into `ConstantIndex`). -/
def noIndexProj : List ProjectionElem → Bool
  | [] => true
  | .index _ :: _ => false
  | .subslice _ _ _ :: _ => false
  | _ :: rest => noIndexProj rest

theorem resolveBorrowProjectionElems_noIndex (locals : List LocalSlot) (proj : List ProjectionElem)
    (h : noIndexProj proj = true) : resolveBorrowProjectionElems locals proj = some proj := by
  induction proj with
  | nil => rfl
  | cons elem rest ih =>
    cases elem <;> simp_all [noIndexProj, resolveBorrowProjectionElems]

theorem projHasSubslice_of_noIndexProj (proj : List ProjectionElem)
    (h : noIndexProj proj = true) : MirSemantics.projHasSubslice proj = false := by
  induction proj with
  | nil => rfl
  | cons elem rest ih =>
    cases elem <;> simp_all [noIndexProj, MirSemantics.projHasSubslice]

/-- The Tree Borrows permission of Anneal's `&raw const` (`Frozen`) and
`&raw mut` (`Active`). -/
def rawPtrPerm : MirAst.Mutability → TreeBorrowPerm
  | .not => .frozen
  | .mut => .active

/-- The Tree Borrows entry that Anneal's `&raw const place` / `&raw mut place`
records for a place that neither starts with `Deref` nor contains `Index`. -/
def rawPtrEntry (tag : Nat) (mutbl : MirAst.Mutability) (place : Place) : BorrowEntry :=
  { tag := tag, targetLocal := place.local_, targetProjection := place.projection,
    perm := rawPtrPerm mutbl }

/-- Anneal's `&raw const place` / `&raw mut place` on a live local whose place
is `Freeze` (`sharedBorrowPerm = .frozen`, e.g. any `ptrTargetSpec` place,
`sharedBorrowPerm_of_ptrTargetSpec`): a fresh tag
`nextTag` names a new Tree Borrows entry for the place, and the resulting
pointer is that tag at offset `0`. The place is not evaluated any further: an
out-of-bounds `ConstantIndex` (or a field that does not exist) is accepted
here and only faults when the pointer is dereferenced, whereas MiniRust's
`AddrOf` evaluates the place and raises UB immediately. -/
theorem evalRvalue_rawPtr_local (locals : List LocalSlot) (mutbl : MirAst.Mutability) (place : Place)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (hsh : sharedBorrowPerm decls layouts place = .frozen)
    (hnd : ∀ rest, place.projection ≠ .deref :: rest) (hni : noIndexProj place.projection = true)
    (slot : LocalSlot) (hs : locals[place.local_]? = some slot) (hlive : slot ≠ .dead)
    (hptr8 : MirSemantics.layoutPointerBytes layouts = 8 := by rfl)
    (hcs : mem.callStack = [] := by rfl) :
    evalRvalue locals (.rawPtr mutbl place) mem decls layouts =
      .ok (.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8) locals
        { mem with borrows := rawPtrEntry mem.nextTag mutbl place :: mem.borrows,
                   nextTag := mem.nextTag + 1 } := by
  obtain ⟨x, proj⟩ := place
  have hres := resolveBorrowProjectionElems_noIndex locals proj hni
  have hsub := projHasSubslice_of_noIndexProj proj hni
  have hlen : length mem.callStack = 0 := by rw [hcs]; rfl
  cases proj with
  | nil =>
    cases slot with
    | dead => exact absurd rfl hlive
    | uninit =>
      cases mutbl <;>
        simp [evalRvalue, MirSemantics.evalRvalueRawPtr, get?, hs, rawPtrEntry, rawPtrPerm, hsh, hptr8, hlen]
    | init v =>
      cases mutbl <;>
        simp [evalRvalue, MirSemantics.evalRvalueRawPtr, get?, hs, rawPtrEntry, rawPtrPerm, hsh, hptr8, hlen]
  | cons e rest =>
    cases e with
    | deref => exact absurd rfl (hnd rest)
    | _ =>
      cases slot with
      | dead => exact absurd rfl hlive
      | uninit =>
        cases mutbl <;>
          simp_all [evalRvalue, MirSemantics.evalRvalueRawPtr, get?, rawPtrEntry, rawPtrPerm]
      | init v =>
        cases mutbl <;>
          simp_all [evalRvalue, MirSemantics.evalRvalueRawPtr, get?, rawPtrEntry, rawPtrPerm]

theorem tyIsFreeze_of_intTypeOf {ty : MirAst.Ty} {it : Gen.IntType}
    (h : intTypeOf ty = some it) :
    tyIsFreeze ty = true := by
  unfold intTypeOf intTyBytes at h
  unfold tyIsFreeze rigidTyIsFreeze
  cases hk : ty.kind <;> simp_all

theorem appendProjections_nil_right (l : List ProjectionElem) :
    appendProjections l [] = l := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [appendProjections, ih]

theorem sharedBorrowPerm_of_ptrTargetSpec {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {place : Place} {pointeeIt : Gen.IntType} {relOff : Nat}
    (h : ptrTargetSpec layouts decls place = some (pointeeIt, relOff)) :
    sharedBorrowPerm decls layouts place = .frozen := by
  rcases place with ⟨k, projs⟩
  cases projs with
  | nil =>
    simp only [ptrTargetSpec] at h
    split at h
    · cases hdk : decls[k]? with
      | none => simp [hdk] at h
      | some d =>
        simp only [hdk, Option.bind_eq_bind, Option.bind_some, Option.map_eq_some_iff] at h
        obtain ⟨it, hit, _⟩ := h
        have hfr := tyIsFreeze_of_intTypeOf hit
        simp [sharedBorrowPerm, placeTy_eq, resolveProjectedTy, get?, hdk, hfr]
    · simp at h
  | cons p1 prest =>
    cases p1 with
    | constantIndex offset minLen fromEnd =>
      cases prest with
      | nil =>
        simp only [ptrTargetSpec] at h
        split at h
        · cases hdk : decls[k]? with
          | none => simp [hdk] at h
          | some d =>
            simp only [hdk, Option.bind_eq_bind, Option.bind_some] at h
            cases ha : arrayTypeOf d.ty with
            | none => simp [ha] at h
            | some apair =>
              obtain ⟨elemIt, count⟩ := apair
              unfold arrayTypeOf at ha
              cases hk : d.ty.kind with
              | array elem n =>
                rw [hk] at ha
                simp only [Option.map_eq_some_iff] at ha
                obtain ⟨⟨s, nb⟩, hb, _⟩ := ha
                have hit : intTypeOf ⟨elem, 0⟩ = some ⟨s, ⟨nb⟩⟩ := by
                  simp [intTypeOf, hb]
                have hfr := tyIsFreeze_of_intTypeOf hit
                have helem : elemTyOf d.ty = some ⟨elem, 0⟩ := by simp [elemTyOf, hk]
                simp [sharedBorrowPerm, placeTy_eq, resolveProjectedTy, get?, hdk, helem, hfr]
              | _ => simp [hk] at ha
        · simp at h
      | cons _ _ => simp [ptrTargetSpec] at h
    | field idx fieldTy =>
      simp only [ptrTargetSpec] at h
      split at h
      · cases hdk : decls[k]? with
        | none => simp [hdk] at h
        | some d =>
          simp only [hdk, Option.bind_eq_bind, Option.bind_some] at h
          cases ht : tupleTypeOf layouts d.ty with
          | none => simp [ht] at h
          | some tpair =>
            obtain ⟨fields, size, align⟩ := tpair
            simp only [ht, Option.bind_some] at h
            cases hres : resolveFieldPath layouts (.tuple fields size align)
                (.field idx fieldTy :: prest) with
            | none => simp [hres] at h
            | some rpair =>
              obtain ⟨relOff', leafSpec⟩ := rpair
              cases leafSpec with
              | tuple _ _ _ => simp [hres] at h
              | scalar leafIt =>
                obtain ⟨leafTy, _, hprojTy, hspecLeaf⟩ :=
                  resolveFieldPath_ty (specOfRigidTy_of_tupleTypeOf ht) hres
                have hit := intTypeOf_of_specOfRigidTy_scalar hspecLeaf
                have hfr := tyIsFreeze_of_intTypeOf hit
                simp [sharedBorrowPerm, placeTy_eq, get?, hdk, hprojTy, hfr]
      · simp at h
    | _ => simp [ptrTargetSpec] at h

theorem mutableBorrowPerm_of_sharedBorrowPerm_frozen {decls : List LocalDecl}
    {layouts : Layout.LayoutTable} {place : Place}
    (h : sharedBorrowPerm decls layouts place = .frozen) :
    MirSemantics.mutableBorrowPerm decls layouts place = .reserved := by
  unfold sharedBorrowPerm at h
  unfold MirSemantics.mutableBorrowPerm
  cases hpt : MirSemantics.placeTy decls layouts place with
  | none => rfl
  | some ty =>
    rw [hpt] at h
    dsimp only at h ⊢
    cases hfr : MirSemantics.tyIsFreeze ty
    · rw [hfr] at h; cases h
    · rfl

theorem sharedBorrowPerm_of_deref_ptrPointeeOf {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {p : Nat} {dp : LocalDecl}
    {srcMutbl : MirAst.Mutability} {pointeeIt : Gen.IntType}
    (hdp : decls[p]? = some dp) (hp : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt)) :
    sharedBorrowPerm decls layouts ⟨p, [.deref]⟩ = .frozen := by
  unfold ptrPointeeOf at hp
  cases hk : dp.ty.kind with
  | rawPtr m inner | ref m inner =>
    rw [hk] at hp
    simp only [Option.map_eq_some_iff] at hp
    obtain ⟨⟨s, nb⟩, hb, _⟩ := hp
    have hit : intTypeOf ⟨inner, 0⟩ = some ⟨s, ⟨nb⟩⟩ := by simp [intTypeOf, hb]
    have hfr := tyIsFreeze_of_intTypeOf hit
    have hpt : pointeeTyOf dp.ty = some ⟨inner, 0⟩ := by simp [pointeeTyOf, hk]
    simp [sharedBorrowPerm, placeTy_eq, resolveProjectedTy, get?, hdp, hpt, hfr]
  | _ => simp [hk] at hp

theorem placeIsZeroSized_of_deref_ptrPointeeOf {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {p : Nat} {dp : LocalDecl}
    {srcMutbl : MirAst.Mutability} {pointeeIt : Gen.IntType}
    (hdp : decls[p]? = some dp) (hp : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt)) :
    MirSemantics.placeIsZeroSized decls layouts ⟨p, [.deref]⟩ = false := by
  unfold ptrPointeeOf at hp
  cases hk : dp.ty.kind with
  | rawPtr m inner | ref m inner =>
    rw [hk] at hp
    simp only [Option.map_eq_some_iff] at hp
    obtain ⟨⟨s, nb⟩, hb, _⟩ := hp
    have hpt : pointeeTyOf dp.ty = some ⟨inner, 0⟩ := by simp [pointeeTyOf, hk]
    have hpl : MirSemantics.placeTy decls layouts ⟨p, [.deref]⟩ = some ⟨inner, 0⟩ := by
      simp [placeTy_eq, resolveProjectedTy, get?, hdp, hpt]
    simp only [MirSemantics.placeIsZeroSized, hpl, MirSemantics.tyIsZeroSized]
    cases inner with
    | int w => cases w <;> rfl
    | uint w => cases w <;> rfl
    | _ => simp [intTyBytes] at hb
  | _ => simp [hk] at hp

/-- The Tree Borrows permission of Anneal's `&place` (`Frozen` on `Freeze`
targets) and `&mut place` / `&two_phase mut place` (`Reserved`). -/
def refBorrowPerm : MirAst.BorrowKind → TreeBorrowPerm
  | .shared => .frozen
  | .mut _ => .reserved

/-- The Tree Borrows entry that Anneal's `&place` / `&mut place` /
`&two_phase mut place` records on a `Freeze` place that neither starts with
`Deref` nor contains `Index`. -/
def refBorrowEntry (tag : Nat) (bkind : MirAst.BorrowKind) (place : Place) : BorrowEntry :=
  { tag := tag, targetLocal := place.local_, targetProjection := place.projection,
    perm := refBorrowPerm bkind }

theorem refBorrowEntry_cases (tag : Nat) (bkind : MirAst.BorrowKind) (place : Place) :
    refBorrowEntry tag bkind place = rawPtrEntry tag (borrowKindMutbl bkind) place ∨
    (borrowKindMutbl bkind = .mut ∧
      refBorrowEntry tag bkind place = { rawPtrEntry tag .mut place with perm := .reserved }) := by
  cases bkind with
  | shared => exact .inl rfl
  | «mut» _ => exact .inr ⟨rfl, rfl⟩

/-- Anneal's `&place`, `&mut place`, or `&two_phase mut place` on a live local
in the fragment: for any target place with `ptrTargetSpec` (all of whose leaf
types are integer and therefore `Freeze`), `.shared` records `.frozen` and
`.mut _` records `.reserved`, matching `refBorrowEntry mem.nextTag bkind place`. -/
theorem evalRvalue_ref_local (locals : List LocalSlot) (bkind : MirAst.BorrowKind)
    (place : Place)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec layouts decls place = some (pointeeIt, relOff))
    (hnd : ∀ rest, place.projection ≠ .deref :: rest) (hni : noIndexProj place.projection = true)
    (slot : LocalSlot) (hs : locals[place.local_]? = some slot) (hlive : slot ≠ .dead)
    (hcs : mem.callStack = [] := by rfl) :
    evalRvalue locals (.ref bkind place) mem decls layouts =
      .ok (.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8) locals
        { mem with borrows := refBorrowEntry mem.nextTag bkind place :: mem.borrows,
                   nextTag := mem.nextTag + 1 } := by
  have hsh := sharedBorrowPerm_of_ptrTargetSpec hspec
  have hmut_p := mutableBorrowPerm_of_sharedBorrowPerm_frozen hsh
  obtain ⟨x, proj⟩ := place
  have hres := resolveBorrowProjectionElems_noIndex locals proj hni
  have hsub := projHasSubslice_of_noIndexProj proj hni
  have hlen : length mem.callStack = 0 := by rw [hcs]; rfl
  cases bkind with
  | shared =>
    cases proj with
    | nil =>
      cases slot with
      | dead => exact absurd rfl hlive
      | uninit => simp [evalRvalue, get?, hs, refBorrowEntry, refBorrowPerm, hsh, hlen]
      | init v => simp [evalRvalue, get?, hs, refBorrowEntry, refBorrowPerm, hsh, hlen]
    | cons e rest =>
      cases e with
      | deref => exact absurd rfl (hnd rest)
      | _ =>
        cases slot with
        | dead => exact absurd rfl hlive
        | uninit => simp_all [evalRvalue, get?, refBorrowEntry, refBorrowPerm]
        | init v => simp_all [evalRvalue, get?, refBorrowEntry, refBorrowPerm]
  | «mut» twoPhase =>
    cases twoPhase <;>
    (cases proj with
    | nil =>
      cases slot with
      | dead => exact absurd rfl hlive
      | uninit => simp [evalRvalue, get?, hs, refBorrowEntry, refBorrowPerm, hmut_p, hlen]
      | init v => simp [evalRvalue, get?, hs, refBorrowEntry, refBorrowPerm, hmut_p, hlen]
    | cons e rest =>
      cases e with
      | deref => exact absurd rfl (hnd rest)
      | _ =>
        cases slot with
        | dead => exact absurd rfl hlive
        | uninit => simp_all [evalRvalue, get?, refBorrowEntry, refBorrowPerm]
        | init v => simp_all [evalRvalue, get?, refBorrowEntry, refBorrowPerm])

/-- The Tree Borrows permission of Anneal's raw reborrow `&raw mutbl *_p` of a
`Freeze` pointee from a parent entry with permission `parentPerm`: `&raw mut`
records `Active`; `&raw const` inherits `Reserved` from a `Reserved` parent and
records `Frozen` otherwise. -/
def rawReborrowPerm : MirAst.Mutability → TreeBorrowPerm → TreeBorrowPerm
  | .not, .reservedFrz c => .reservedFrz c
  | .not, .reservedIM => .reservedIM
  | .not, .cell => .cell
  | .not, _ => .frozen
  | .mut, _ => .active

/-- Anneal's Tree Borrows entry for a raw reborrow `&raw mutbl *_p` through the
parent entry `parent` named by `parentTag`: a child of `parentTag` on the
parent's target place and byte range. -/
def rawReborrowEntry (tag : Nat) (mutbl : MirAst.Mutability) (parent : BorrowEntry)
    (parentTag : Nat) : BorrowEntry :=
  { tag := tag, targetLocal := parent.targetLocal, targetProjection := parent.targetProjection,
    perm := rawReborrowPerm mutbl parent.perm, rangeOffset := parent.rangeOffset,
    rangeLen := parent.rangeLen, parentTag := some parentTag,
    targetFrameDepth := parent.targetFrameDepth, allocDead := parent.allocDead }

/-- The Tree Borrows permission of Anneal's reference reborrow of a `Freeze`
pointee: `&*_p` records `Frozen`, and `&mut *_p` / `&two_phase mut *_p` record
`Reserved` (lazy activation on the first child write). -/
def refReborrowPerm : MirAst.BorrowKind → TreeBorrowPerm
  | .shared => .frozen
  | .mut _ => .reserved

/-- Anneal's Tree Borrows entry for a reference reborrow `&*_p` / `&mut *_p`
through the parent entry `parent` named by `parentTag`. -/
def refReborrowEntry (tag : Nat) (bkind : MirAst.BorrowKind) (parent : BorrowEntry)
    (parentTag : Nat) : BorrowEntry :=
  { tag := tag, targetLocal := parent.targetLocal, targetProjection := parent.targetProjection,
    perm := refReborrowPerm bkind, rangeOffset := parent.rangeOffset,
    rangeLen := parent.rangeLen, parentTag := some parentTag,
    targetFrameDepth := parent.targetFrameDepth, allocDead := parent.allocDead }

/-- Anneal's raw address-of `&raw const *_p` / `&raw mut *_p` (RFC 2582): when
`_p` holds an 8-byte provenance pointer `.ptr parentPtr 8` and `safeRefOk` holds
(automatic for raw pointer locals `_p`, or checked via `checkSafeRefDerefOk` for
safe reference locals `_p`), returns `.ok (.ptr parentPtr 8) locals mem` directly
without allocating a fresh borrow tag or dereferencing the pointee. -/
theorem evalRvalue_rawPtr_reborrow (locals : List LocalSlot) (mutbl : MirAst.Mutability)
    (p : Nat) (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (dp : LocalDecl) (srcMutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (hdp : decls[p]? = some dp) (_hp_ty : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt))
    (parentPtr : ProvenancePtr) (hp : locals[p]? = some (.init (.ptr parentPtr 8)))
    (hsafe :
      (match dp.ty.kind with
       | .ref _ _ =>
         MirSemantics.checkSafeRefDerefOk locals parentPtr mem.borrows mem.globals
           mem.callerLocals decls layouts
           (MirSemantics.placeTyResolved decls layouts ⟨p, [.deref]⟩) mem.callStack
       | _ => true) = true)
    (hptr8 : MirSemantics.layoutPointerBytes layouts = 8 := by rfl) :
    evalRvalue locals (.rawPtr mutbl ⟨p, [.deref]⟩) mem decls layouts =
      .ok (.ptr parentPtr 8) locals mem := by
  rcases dp with ⟨_, ⟨kind, _⟩, _⟩
  unfold evalRvalue MirSemantics.evalRvalueRawPtr
  rw [hptr8]
  dsimp only [get?, MirSemantics.stripTransparentProjections] at hsafe ⊢
  rw [hdp, hp]
  cases kind <;> simp_all

/-- Anneal's reborrow `&*_p` / `&mut *_p` / `&two_phase mut *_p` through an
initialized pointer or reference local `_p` to an integer whose entry
`parentEntry` has compatible permission (`.active` or `.reserved` for mutable
reborrows) and whose target local is initialized (`targetRootVal`) and resolves
via `resolveRefDerefTarget?` to `(parentEntry.targetProjection, 0)`: performs
the initial read through `_p`'s tag (`freezeTreeBorrowsOnReadAtProj`, freezing
foreign `.active` entries overlapping the parent's target,
`PermissionUnprot::init_access`) and pushes the child entry `refReborrowEntry`. -/
theorem evalRvalue_ref_reborrow (locals : List LocalSlot) (bkind : MirAst.BorrowKind)
    (p : Nat)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (dp : LocalDecl) (srcMutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (hdp : decls[p]? = some dp) (hp_ty : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt))
    (parentPtr : ProvenancePtr) (hp : locals[p]? = some (.init (.ptr parentPtr 8)))
    (hoff0 : parentPtr.offsetBytes = 0)
    (parentEntry : BorrowEntry) (he : lookupBorrow mem.borrows parentPtr.tag = some parentEntry)
    (hndis : parentEntry.perm ≠ .disabled)
    (hmut : borrowKindMutbl bkind = .mut → parentEntry.perm = .active ∨ parentEntry.perm = .reserved)
    (targetRootVal : Value) (ht : locals[parentEntry.targetLocal]? = some (.init targetRootVal))
    (hres :
      MirSemantics.resolveRefDerefTarget? locals targetRootVal parentEntry parentPtr [] decls
        layouts (MirSemantics.placeTyResolved decls layouts ⟨p, [.deref]⟩)
        (MirSemantics.placeTyResolved decls layouts ⟨p, [.deref]⟩) false decls =
        some (some (parentEntry.targetProjection, 0)))
    (hrub :
      MirSemantics.hasTreeReadUB mem.borrows mem.borrows mem.activeProtectors
        parentEntry.targetLocal (some parentPtr.tag) parentEntry.targetProjection
        parentEntry.rangeOffset parentEntry.rangeLen parentEntry.targetFrameDepth = false)
    (hptr8 : MirSemantics.layoutPointerBytes layouts = 8 := by rfl)
    (hcs : mem.callStack = [] := by rfl) :
    evalRvalue locals (.ref bkind ⟨p, [.deref]⟩) mem decls layouts =
      .ok (.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8) locals
        { mem with
          borrows := refReborrowEntry mem.nextTag bkind parentEntry parentPtr.tag ::
            MirSemantics.freezeTreeBorrowsOnReadAtProj mem.borrows mem.borrows
              parentEntry.targetLocal (some parentPtr.tag) parentEntry.targetProjection
              parentEntry.rangeOffset parentEntry.rangeLen mem.activeProtectors
              parentEntry.targetFrameDepth,
          nextTag := mem.nextTag + 1 } := by
  have hsh : sharedBorrowPerm decls layouts ⟨p, [.deref]⟩ = .frozen :=
    sharedBorrowPerm_of_deref_ptrPointeeOf hdp hp_ty
  have hmut_p : MirSemantics.mutableBorrowPerm decls layouts ⟨p, [.deref]⟩ = .reserved :=
    mutableBorrowPerm_of_sharedBorrowPerm_frozen hsh
  have hzst : MirSemantics.placeIsZeroSized decls layouts ⟨p, [.deref]⟩ = false :=
    placeIsZeroSized_of_deref_ptrPointeeOf hdp hp_ty
  unfold evalRvalue MirSemantics.evalRvalueRefDeref
  rw [hptr8, hcs]
  dsimp only [get?, MirSemantics.stripTransparentProjections, resolveBorrowProjectionElems,
    MirSemantics.activeFrameSlot?]
  rw [hp]
  dsimp only
  rw [hoff0]
  dsimp only [MirSemantics.checkDerefAlign, Nat.beq_refl, Bool.and_self]
  rw [he]
  dsimp only
  rw [ht]
  dsimp only
  rw [hres]
  cases bkind with
  | shared =>
    rw [hsh, hzst]
    cases hpe : parentEntry.perm with
    | disabled => exact absurd hpe hndis
    | cell | reservedFrz _ | reservedIM | unique | frozen =>
      dsimp only
      cases hbs : mem.borrows with
      | nil => rfl
      | cons b1 rest =>
        cases rest with
        | nil => rfl
        | cons b2 bs =>
          rw [hbs] at hrub
          rw [hrub]
          rfl
  | «mut» twoPhase =>
    rw [hmut_p, hzst]
    rcases hmut rfl with hpe | hpe <;>
    cases twoPhase <;>
      (rw [hpe]; dsimp only;
       cases hbs : mem.borrows with
       | nil => rfl
       | cons b1 rest =>
         cases rest with
         | nil => rfl
         | cons b2 bs =>
           rw [hbs] at hrub
           rw [hrub]
           rfl)

theorem rigidTyByteSize_of_ptrPointeeOf (layouts : Layout.LayoutTable) {t : MirAst.Ty}
    {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (hp : ptrPointeeOf t = some (mutbl, it)) :
    MirSemantics.rigidTyByteSize layouts t = some 8 := by
  unfold ptrPointeeOf at hp
  cases hk : t.kind with
  | rawPtr m inner | ref m inner =>
    rw [hk] at hp
    cases inner <;> simp_all [intTyBytes, MirSemantics.rigidTyByteSize, MirSemantics.rigidTyKindByteSize]
  | _ => rw [hk] at hp; cases hp

theorem encodeValueToBytes_of_ptrPointeeOf (layouts : Layout.LayoutTable) {t : MirAst.Ty}
    {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (hp : ptrPointeeOf t = some (mutbl, it)) (pv : ProvenancePtr) (hoff : pv.offsetBytes = 0) :
    MirSemantics.encodeValueToBytes MirSemantics.defaultCodecFuel layouts t (.ptr pv 8) =
      MirSemantics.encodeScalarBytes ⟨0, 8⟩ (.some (pv.allocId, pv.tag)) := by
  unfold ptrPointeeOf at hp
  cases hk : t.kind with
  | rawPtr m inner | ref m inner =>
    rw [hk] at hp
    cases inner <;>
      simp_all [intTyBytes, MirSemantics.encodeValueToBytes]
  | _ => rw [hk] at hp; cases hp

theorem decodeValueFromBytes_of_ptrPointeeOf (layouts : Layout.LayoutTable) {t : MirAst.Ty}
    {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (hp : ptrPointeeOf t = some (mutbl, it)) (pv : ProvenancePtr) (hoff : pv.offsetBytes = 0)
    {bs : List MirSemantics.AbstractByte}
    (hbs : MirSemantics.encodeScalarBytes ⟨0, 8⟩ (.some (pv.allocId, pv.tag)) = some bs) :
    MirSemantics.decodeValueFromBytes MirSemantics.defaultCodecFuel layouts t bs =
      some (.ptr pv 8) ∧ bs.length = 8 := by
  have hpv : ({ allocId := pv.allocId, offsetBytes := 0 } : ProvenancePtr) = pv := by
    cases pv; simp_all
  simp only [MirSemantics.encodeScalarBytes, MirSemantics.encodeLittleEndianBytes,
    Option.some.injEq] at hbs
  subst hbs
  refine ⟨?_, rfl⟩
  unfold ptrPointeeOf at hp
  cases hk : t.kind with
  | rawPtr m inner | ref m inner =>
    rw [hk] at hp
    cases inner <;> simp [intTyBytes] at hp <;>
      (simp only [MirSemantics.decodeValueFromBytes, hk];
       exact congrArg (some ∘ (Value.ptr · 8)) hpv)
  | _ => rw [hk] at hp; cases hp

theorem decodeTypedValueFromBytes_of_ptrPointeeOf (layouts : Layout.LayoutTable) {t : MirAst.Ty}
    {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (hp : ptrPointeeOf t = some (mutbl, it)) (pv : ProvenancePtr) (hoff : pv.offsetBytes = 0)
    {bs : List MirSemantics.AbstractByte}
    (hbs : MirSemantics.encodeScalarBytes ⟨0, 8⟩ (.some (pv.allocId, pv.tag)) = some bs)
    (hptr8 : MirSemantics.layoutPointerBytes layouts = 8 := by rfl) :
    MirSemantics.decodeTypedValueFromBytes MirSemantics.defaultCodecFuel layouts t bs =
      some (.ptr pv 8) ∧ bs.length = 8 := by
  have hpv : ({ allocId := pv.allocId, offsetBytes := 0 } : ProvenancePtr) = pv := by
    cases pv; simp_all
  simp only [MirSemantics.encodeScalarBytes, MirSemantics.encodeLittleEndianBytes,
    Option.some.injEq] at hbs
  subst hbs
  refine ⟨?_, rfl⟩
  unfold ptrPointeeOf at hp
  rcases t with ⟨kind, lidx⟩
  cases kind with
  | rawPtr m inner | ref m inner =>
    cases inner <;> simp [intTyBytes] at hp <;>
      (dsimp only [MirSemantics.decodeTypedValueFromBytes, MirSemantics.defaultCodecFuel,
         MirSemantics.normalizeCodecTy];
       rw [hptr8];
       simp only [MirSemantics.decodePtrBytesNoForge, MirSemantics.abstractBytesUniformProv,
         MirSemantics.abstractBytesAllProvAux, Nat.beq_refl, Bool.and_self];
       exact congrArg (some ∘ (Value.ptr · 8)) hpv)
  | _ => simp at hp

theorem ptrPointeeOf_resolveTyWithLocalDecls (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (t : MirAst.Ty) :
    ptrPointeeOf (MirSemantics.resolveTyWithLocalDecls decls layouts t) = ptrPointeeOf t := by
  simp only [ptrPointeeOf, resolveTyWithLocalDecls_kind]

theorem tyByteSize_of_ptrPointeeOf (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) {t : MirAst.Ty} {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (hp : ptrPointeeOf t = some (mutbl, it)) :
    MirSemantics.tyByteSize decls layouts t = some 8 := by
  have hr : ptrPointeeOf (MirSemantics.resolveTyWithLocalDecls decls layouts t) = some (mutbl, it) := by
    rw [ptrPointeeOf_resolveTyWithLocalDecls]; exact hp
  have hsz := rigidTyByteSize_of_ptrPointeeOf layouts hr
  unfold MirSemantics.tyByteSize MirSemantics.tyByteSizeAndAlignAux
  unfold ptrPointeeOf at hr
  rcases hrt : MirSemantics.resolveTyWithLocalDecls decls layouts t with ⟨kind, lidx⟩
  rw [hrt] at hr hsz
  cases kind with
  | rawPtr m inner | ref m inner =>
    dsimp only
    rw [hsz]
  | _ => simp at hr

theorem encodeByteCastSourceBytes_of_ptrPointeeOf (layouts : Layout.LayoutTable) {t : MirAst.Ty}
    {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (hp : ptrPointeeOf t = some (mutbl, it)) (pv : ProvenancePtr) (hoff : pv.offsetBytes = 0) :
    MirSemantics.encodeByteCastSourceBytes layouts t (.ptr pv 8) =
      MirSemantics.encodeScalarBytes ⟨0, 8⟩ (.some (pv.allocId, pv.tag)) := by
  have henc := encodeValueToBytes_of_ptrPointeeOf layouts hp pv hoff
  unfold MirSemantics.encodeByteCastSourceBytes MirSemantics.encodeTypedValueToBytes
  unfold ptrPointeeOf at hp
  rcases t with ⟨kind, lidx⟩
  cases kind with
  | rawPtr m inner | ref m inner =>
    dsimp only [MirSemantics.normalizeCodecTy, MirSemantics.isUnionLayout]
    rw [henc]
  | _ => simp at hp

/-- Anneal's `CastKind::Transmute` (`evalByteCast`) from a thin pointer or
reference local `p` (`ptrPointeeOf dp.ty = some _`) to a thin pointer or
reference type `castTy` (`ptrPointeeOf castTy = some _`): preserves an
8-byte zero-offset provenance pointer `.ptr pv 8` and raises `.ub` when `p` is
uninitialized or dead. -/
theorem evalRvalue_transmute_ptr (locals : List LocalSlot) (p : Nat) (castTy : MirAst.Ty)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    {dp : LocalDecl} {srcMutbl dstMutbl : MirAst.Mutability} {srcIt dstIt : Gen.IntType}
    (hdp : decls[p]? = some dp)
    (hsrc : ptrPointeeOf dp.ty = some (srcMutbl, srcIt))
    (hdst : ptrPointeeOf castTy = some (dstMutbl, dstIt))
    (hptr8 : MirSemantics.layoutPointerBytes layouts = 8 := by rfl) :
    (∀ pv, pv.offsetBytes = 0 → locals[p]? = some (.init (.ptr pv 8)) →
      evalRvalue locals (.cast .transmute (.copy ⟨p, []⟩) castTy) mem decls layouts =
        .ok (.ptr pv 8) locals mem) ∧
    ((locals[p]? = some .uninit ∨ locals[p]? = some .dead) →
      evalRvalue locals (.cast .transmute (.copy ⟨p, []⟩) castTy) mem decls layouts = .ub) := by
  refine ⟨fun pv hoff hpv => ?_, fun hu => ?_⟩
  · have hrSrc : ptrPointeeOf (MirSemantics.resolveTyWithLocalDecls decls layouts dp.ty) =
        some (srcMutbl, srcIt) := by
      rw [ptrPointeeOf_resolveTyWithLocalDecls]; exact hsrc
    have hrDst : ptrPointeeOf (MirSemantics.resolveTyWithLocalDecls decls layouts castTy) =
        some (dstMutbl, dstIt) := by
      rw [ptrPointeeOf_resolveTyWithLocalDecls]; exact hdst
    have hszSrc := tyByteSize_of_ptrPointeeOf decls layouts hrSrc
    have hszDst := tyByteSize_of_ptrPointeeOf decls layouts hrDst
    have hopTy : MirSemantics.operandTy decls layouts (.copy ⟨p, []⟩) = some dp.ty := by
      simp [MirSemantics.operandTy, MirSemantics.placeTy, MirSemantics.resolveProjectedTy, get?, hdp]
    have henc := encodeByteCastSourceBytes_of_ptrPointeeOf layouts hrSrc pv hoff
    obtain ⟨bs, hbs⟩ : ∃ bs, MirSemantics.encodeScalarBytes ⟨0, 8⟩ (.some (pv.allocId, pv.tag)) = some bs :=
      ⟨_, rfl⟩
    rw [hbs] at henc
    obtain ⟨hdec, hlen⟩ := decodeTypedValueFromBytes_of_ptrPointeeOf layouts hrDst pv hoff hbs hptr8
    have hlenEq : Nat.beq (Trusted.Sequence.length bs) 8 = true := by
      have : Trusted.Sequence.length bs = bs.length := rfl
      simp [this, hlen]
    simp [evalRvalue, evalByteCast, MirSemantics.resolveByteCastSrcTyAndSize,
      evalOperand, get?, hpv, readProjectedValue,
      hszDst, hopTy, hszSrc, henc, hlenEq, hdec]
  · rcases hu with hu | hu <;>
      simp [evalRvalue, evalByteCast, evalOperand, get?, hu]

/-- Reborrowing a `Frozen` pointer or reference as `&mut *_p` is UB in Anneal's
Tree Borrows model. -/
theorem evalRvalue_ref_reborrow_frozen_mut_ub (locals : List LocalSlot) (twoPhase : Bool)
    (p : Nat) (restProj : List ProjectionElem)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (parentPtr : ProvenancePtr) (hp : locals[p]? = some (.init (.ptr parentPtr 8)))
    (hoff0 : parentPtr.offsetBytes = 0)
    (parentEntry : BorrowEntry) (he : lookupBorrow mem.borrows parentPtr.tag = some parentEntry)
    (hfr : parentEntry.perm = .frozen)
    (hptr8 : MirSemantics.layoutPointerBytes layouts = 8 := by rfl) :
    evalRvalue locals (.ref (.mut twoPhase) ⟨p, .deref :: restProj⟩) mem decls layouts = .ub := by
  unfold evalRvalue MirSemantics.evalRvalueRefDeref
  rw [hptr8]
  dsimp only [get?]
  rw [hp]
  dsimp only
  rw [hoff0]
  dsimp only [MirSemantics.checkDerefAlign, Nat.beq_refl, Bool.and_self]
  rw [he]
  dsimp only
  rw [hfr]
  rfl

/-- Reborrowing a `Disabled` pointer or reference as `&*_p` or `&mut *_p` is UB
in Anneal's Tree Borrows model. -/
theorem evalRvalue_ref_reborrow_disabled_ub (locals : List LocalSlot) (bkind : MirAst.BorrowKind)
    (p : Nat) (restProj : List ProjectionElem)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (parentPtr : ProvenancePtr) (hp : locals[p]? = some (.init (.ptr parentPtr 8)))
    (hoff0 : parentPtr.offsetBytes = 0)
    (parentEntry : BorrowEntry) (he : lookupBorrow mem.borrows parentPtr.tag = some parentEntry)
    (hdis : parentEntry.perm = .disabled)
    (hptr8 : MirSemantics.layoutPointerBytes layouts = 8 := by rfl) :
    evalRvalue locals (.ref bkind ⟨p, .deref :: restProj⟩) mem decls layouts = .ub := by
  unfold evalRvalue MirSemantics.evalRvalueRefDeref
  rw [hptr8]
  dsimp only [get?]
  rw [hp]
  dsimp only
  rw [hoff0]
  dsimp only [MirSemantics.checkDerefAlign, Nat.beq_refl, Bool.and_self]
  rw [he]
  dsimp only
  rw [hdis]
  rfl

/-- Under RFC 2582, `&raw mut *_p` through a raw pointer or non-disabled reference
does not reborrow or fault on a `Frozen` tag; it preserves `parentPtr` (whereas
on a `Disabled` safe reference `_p`, `checkSafeRefDerefOk` raises `.ub`). -/
theorem evalRvalue_rawPtr_reborrow_frozen_mut_ub (locals : List LocalSlot)
    (p : Nat)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (dp : LocalDecl) (srcMutbl : MirAst.Mutability) (pointeeTy : MirAst.RigidTy)
    (hdp : decls[p]? = some dp) (hraw : dp.ty.kind = .rawPtr srcMutbl pointeeTy)
    (parentPtr : ProvenancePtr) (hp : locals[p]? = some (.init (.ptr parentPtr 8)))
    (hptr8 : MirSemantics.layoutPointerBytes layouts = 8 := by rfl) :
    evalRvalue locals (.rawPtr .mut ⟨p, [.deref]⟩) mem decls layouts =
      .ok (.ptr parentPtr 8) locals mem := by
  rcases dp with ⟨_, ⟨kind, _⟩, _⟩
  dsimp only at hraw
  subst hraw
  unfold evalRvalue MirSemantics.evalRvalueRawPtr
  rw [hptr8]
  dsimp only [get?, MirSemantics.stripTransparentProjections]
  rw [hdp, hp]
  rfl

/-- Taking `&raw const *_p` or `&raw mut *_p` through a `Disabled` safe reference
local `_p` (`dp.ty.kind = .ref _ _`) is UB in Anneal's Tree Borrows model
(`checkSafeRefDerefOk`). -/
theorem evalRvalue_rawPtr_reborrow_disabled_ub (locals : List LocalSlot) (mutbl : MirAst.Mutability)
    (p : Nat) (restProj : List ProjectionElem)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (dp : LocalDecl) (srcMutbl : MirAst.Mutability) (pointeeTy : MirAst.RigidTy)
    (hdp : decls[p]? = some dp) (href : dp.ty.kind = .ref srcMutbl pointeeTy)
    (parentPtr : ProvenancePtr) (hp : locals[p]? = some (.init (.ptr parentPtr 8)))
    (hoff0 : parentPtr.offsetBytes = 0)
    (parentEntry : BorrowEntry) (he : lookupBorrow mem.borrows parentPtr.tag = some parentEntry)
    (hdis : parentEntry.perm = .disabled)
    (hptr8 : MirSemantics.layoutPointerBytes layouts = 8 := by rfl) :
    evalRvalue locals (.rawPtr mutbl ⟨p, .deref :: restProj⟩) mem decls layouts = .ub := by
  rcases dp with ⟨_, ⟨kind, _⟩, _⟩
  dsimp only at href
  subst href
  unfold evalRvalue MirSemantics.evalRvalueRawPtr
  rw [hptr8]
  dsimp only [get?, MirSemantics.checkSafeRefDerefOk]
  rw [hdp, hp]
  dsimp only
  rw [hoff0]
  dsimp only [MirSemantics.checkDerefAlign, Nat.beq_refl]
  rw [he]
  dsimp only
  rw [hdis]
  rfl

/-- Reborrowing an uninitialized or dead pointer/reference local `_p` is UB in
Anneal. -/
theorem evalRvalue_reborrow_ub_of_not_init (locals : List LocalSlot) (p : Nat)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (h : locals[p]? = some .uninit ∨ locals[p]? = some .dead) :
    (∀ mutbl, evalRvalue locals (.rawPtr mutbl ⟨p, [.deref]⟩) mem decls layouts = .ub) ∧
    (∀ bkind, evalRvalue locals (.ref bkind ⟨p, [.deref]⟩) mem decls layouts = .ub) := by
  rcases h with hu | hd
  · refine ⟨fun _ => ?_, fun _ => ?_⟩
    · unfold evalRvalue MirSemantics.evalRvalueRawPtr; dsimp only [get?]; rw [hu]
    · unfold evalRvalue MirSemantics.evalRvalueRefDeref; dsimp only [get?]; rw [hu]
  · refine ⟨fun _ => ?_, fun _ => ?_⟩
    · unfold evalRvalue MirSemantics.evalRvalueRawPtr; dsimp only [get?]; rw [hd]
    · unfold evalRvalue MirSemantics.evalRvalueRefDeref; dsimp only [get?]; rw [hd]

/-! ## MiniRust: `ReborrowSettings::new` and `Statement::Validate` (`spec/mem/tree_borrows/reborrow_settings.md`) -/

theorem cellsToFreezeMask_nil (sz : Size) :
    cellsToFreezeMask [] sz = .ok (List.replicate sz.bytes true) := by
  simp [cellsToFreezeMask, cellsToFreezeMaskLoop]

theorem cellsToFreezeMask_single_full (sz : Size) :
    cellsToFreezeMask [(⟨0⟩, sz)] sz = .ok (List.replicate sz.bytes false) := by
  simp [cellsToFreezeMask, cellsToFreezeMaskLoop]

theorem mapM_replicate_ok {α β : Type} (n : Nat) (x : α) (f : α → Interp β) (y : β)
    (hy : f x = .ok y) :
    (List.replicate n x).mapM f = .ok (List.replicate n y) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.mapM_cons, hy, ok_bind, ih, pure_ok]

/-- `ReborrowSettings::new` on a shared reference `&T` to a `Freeze` scalar
type (`fn_entry = false`) assigns `Permission::Unprot(PermissionUnprot::Frozen)`
across all `it.size.bytes` inside bytes and outside, with `Protected::No`. -/
theorem reborrowSettings_shared_freeze {Provenance : Type}
    (vtableLookup : Gen.ThinPointer Provenance → Interp Gen.VTable)
    (ptr : Gen.Pointer Provenance) (it : Gen.IntType)
    (params : Gen.TreeBorrowsParams) (fnImplicitWrites : Bool) :
    ReborrowSettings.new vtableLookup ptr (refPtrType .not it) false params fnImplicitWrites =
      .ok (some {
        inside := List.replicate it.size.bytes (.Unprot .Frozen)
        outside := .Unprot .Frozen
        «protected» := .No
      }) := by
  have hmask : UnsafeCellStrategy.freeze_mask vtableLookup (.Sized []) (.Sized it.size ⟨it.size.bytes⟩) ptr.metadata =
      .ok (List.replicate it.size.bytes true) := cellsToFreezeMask_nil it.size
  have hmap : (List.replicate it.size.bytes true).mapM
      (fun freeze => ReborrowSettings.perm (refPtrType .not it) .No false true freeze) =
      .ok (List.replicate it.size.bytes (.Unprot .Frozen)) :=
    mapM_replicate_ok it.size.bytes true _ (Gen.Permission.Unprot .Frozen) rfl
  simp only [refPtrType, translateMutbl, intPointeeInfo] at hmap
  simp only [ReborrowSettings.new, refPtrType, translateMutbl, intPointeeInfo,
    PtrType.safe_pointee, Protected.yes, Bool.false_eq_true, ↓reduceIte,
    ne_eq, not_true_eq_false, decide_false, Bool.false_and,
    hmask, ok_bind, hmap]
  rfl

/-- `ReborrowSettings::new` on a mutable reference `&mut T` to a `Freeze`,
`Unpin` scalar type (`fn_entry = false`) assigns
`Permission::Unprot(PermissionUnprot::Reserved)` across all `it.size.bytes`
inside bytes and outside, with `Protected::No`. -/
theorem reborrowSettings_mut_freeze_default {Provenance : Type}
    (vtableLookup : Gen.ThinPointer Provenance → Interp Gen.VTable)
    (ptr : Gen.Pointer Provenance) (it : Gen.IntType)
    (params : Gen.TreeBorrowsParams) (fnImplicitWrites : Bool) :
    ReborrowSettings.new vtableLookup ptr (refPtrType .mut it) false params fnImplicitWrites =
      .ok (some {
        inside := List.replicate it.size.bytes (.Unprot .Reserved)
        outside := .Unprot .Reserved
        «protected» := .No
      }) := by
  have hmask : UnsafeCellStrategy.freeze_mask vtableLookup (.Sized []) (.Sized it.size ⟨it.size.bytes⟩) ptr.metadata =
      .ok (List.replicate it.size.bytes true) := cellsToFreezeMask_nil it.size
  have hmap : (List.replicate it.size.bytes true).mapM
      (fun freeze => ReborrowSettings.perm (refPtrType .mut it) .No false true freeze) =
      .ok (List.replicate it.size.bytes (.Unprot .Reserved)) :=
    mapM_replicate_ok it.size.bytes true _ (Gen.Permission.Unprot .Reserved) rfl
  simp only [refPtrType, translateMutbl, intPointeeInfo] at hmap
  simp only [ReborrowSettings.new, refPtrType, translateMutbl, intPointeeInfo,
    PtrType.safe_pointee, Protected.yes, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    ne_eq, not_true_eq_false, decide_false, Bool.false_and,
    hmask, ok_bind, hmap]
  rfl

/-- `ReborrowSettings::new` on a function-entry mutable reference `&mut T` to a
`Freeze`, `Unpin` scalar type (`fn_entry = true`) with implicit writes disabled
assigns `Permission::Prot(PermissionProt::Reserved { had_local_read: false, had_foreign_read: false })`
inside and outside, with `Protected::Strong`. -/
theorem reborrowSettings_mut_freeze_fnEntry_noImplicit {Provenance : Type}
    (vtableLookup : Gen.ThinPointer Provenance → Interp Gen.VTable)
    (ptr : Gen.Pointer Provenance) (it : Gen.IntType) :
    ReborrowSettings.new vtableLookup ptr (refPtrType .mut it) true ⟨false⟩ true =
      .ok (some {
        inside := List.replicate it.size.bytes (.Prot (.Reserved false false))
        outside := .Prot (.Reserved false false)
        «protected» := .Strong
      }) := by
  have hmask : UnsafeCellStrategy.freeze_mask vtableLookup (.Sized []) (.Sized it.size ⟨it.size.bytes⟩) ptr.metadata =
      .ok (List.replicate it.size.bytes true) := cellsToFreezeMask_nil it.size
  have hmap : (List.replicate it.size.bytes true).mapM
      (fun freeze => ReborrowSettings.perm (refPtrType .mut it) .Strong false true freeze) =
      .ok (List.replicate it.size.bytes (.Prot (.Reserved false false))) :=
    mapM_replicate_ok it.size.bytes true _ (Gen.Permission.Prot (.Reserved false false)) rfl
  simp only [refPtrType, translateMutbl, intPointeeInfo] at hmap
  simp only [ReborrowSettings.new, refPtrType, translateMutbl, intPointeeInfo,
    PtrType.safe_pointee, Protected.yes, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Bool.and_false, Bool.false_and, hmask, ok_bind, hmap]
  rfl

/-- `ReborrowSettings::new` on a function-entry mutable reference `&mut T` to a
`Freeze`, `Unpin` scalar type (`fn_entry = true`) with implicit writes enabled
assigns `Permission::Prot(PermissionProt::Unique)` inside and
`Permission::Prot(PermissionProt::Reserved { had_local_read: false, had_foreign_read: false })`
outside, with `Protected::Strong`. -/
theorem reborrowSettings_mut_freeze_fnEntry_implicitWrite {Provenance : Type}
    (vtableLookup : Gen.ThinPointer Provenance → Interp Gen.VTable)
    (ptr : Gen.Pointer Provenance) (it : Gen.IntType) :
    ReborrowSettings.new vtableLookup ptr (refPtrType .mut it) true ⟨true⟩ true =
      .ok (some {
        inside := List.replicate it.size.bytes (.Prot .Unique)
        outside := .Prot (.Reserved false false)
        «protected» := .Strong
      }) := by
  have hmask : UnsafeCellStrategy.freeze_mask vtableLookup (.Sized []) (.Sized it.size ⟨it.size.bytes⟩) ptr.metadata =
      .ok (List.replicate it.size.bytes true) := cellsToFreezeMask_nil it.size
  have hmap : (List.replicate it.size.bytes true).mapM
      (fun freeze => ReborrowSettings.perm (refPtrType .mut it) .Strong true true freeze) =
      .ok (List.replicate it.size.bytes (.Prot .Unique)) :=
    mapM_replicate_ok it.size.bytes true _ (Gen.Permission.Prot .Unique) rfl
  simp only [refPtrType, translateMutbl, intPointeeInfo] at hmap
  simp only [ReborrowSettings.new, refPtrType, translateMutbl, intPointeeInfo,
    PtrType.safe_pointee, Protected.yes, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    ne_eq, reduceCtorEq, not_false_eq_true, decide_true, Bool.and_true,
    hmask, ok_bind, hmap]
  rfl

/-- Unprotected `Reserved` and `ReservedIm` permissions tolerate foreign reads
(`spec/mem/tree_borrows/state_machine_unprotected.md`). -/
theorem PermissionUnprot.reserved_foreign_read_eq :
    PermissionUnprot.transition .Reserved .Read .Foreign = .ok .Reserved ∧
    PermissionUnprot.transition .ReservedIm .Read .Foreign = .ok .ReservedIm :=
  ⟨rfl, rfl⟩

/-- In unprotected Tree Borrows, a local (or child) write activates `Reserved`
and `ReservedIm` to `Unique` (`spec/mem/tree_borrows/state_machine.md`). -/
theorem Permission.local_write_activates_unprot_reserved :
    Permission.transition (.Unprot .Reserved) .Write .Local = .ok (.Unprot .Unique) ∧
    Permission.transition (.Unprot .ReservedIm) .Write .Local = .ok (.Unprot .Unique) :=
  ⟨rfl, rfl⟩

/-- In unprotected Tree Borrows, a foreign write disables a `Freeze` `Reserved`
borrow (`PermissionUnprot::Reserved`) while keeping an interior-mutable `!Freeze`
`ReservedIm` borrow (`PermissionUnprot::ReservedIm`) in `ReservedIm`. -/
theorem Permission.foreign_write_unprot_reserved_iff :
    Permission.transition (.Unprot .Reserved) .Write .Foreign = .ok (.Unprot .Disabled) ∧
    Permission.transition (.Unprot .ReservedIm) .Write .Foreign = .ok (.Unprot .ReservedIm) :=
  ⟨rfl, rfl⟩

/-- Protected `Reserved` permissions record foreign reads (`had_foreign_read := true`)
and subsequently reject local/child writes as UB, preventing activation after
a foreign read while the protector is live
(`spec/mem/tree_borrows/state_machine_protected.md`). -/
theorem PermissionProt.reserved_foreign_read_blocks_local_write (hl : Bool) :
    PermissionProt.transition (.Reserved hl false) .Read .Foreign = .ok (.Reserved hl true) ∧
    PermissionProt.transition (.Reserved hl true) .Write .Local =
      .error (.ub "Tree Borrows: local write to protected Reserved reference that had a foreign read") :=
  ⟨rfl, rfl⟩

/-- Unprotected permissions never prevent deallocation
(`PermissionUnprot::prevents_deallocation`). -/
theorem PermissionUnprot.prevents_deallocation_false (p : Gen.PermissionUnprot) :
    PermissionUnprot.prevents_deallocation p = false :=
  rfl

/-- Protected permissions prevent deallocation if and only if they are `Unique`
or have already undergone a local read (`Reserved true _` or `Frozen true`)
(`PermissionProt::prevents_deallocation`, `spec/mem/tree_borrows/state_machine_protected.md`). -/
theorem PermissionProt.prevents_deallocation_iff (p : Gen.PermissionProt) :
    PermissionProt.prevents_deallocation p = true ↔
      (p = .Unique ∨ (∃ hf, p = .Reserved true hf) ∨ p = .Frozen true) := by
  cases p <;> simp [PermissionProt.prevents_deallocation]

/-- `ReborrowSettings::new` on a shared reference `&UnsafeCell<T>` (`freeze = false`,
`unsafe_cells = .Sized [(⟨0⟩, sz)]`, `fn_entry = false`) assigns
`Permission::Unprot(PermissionUnprot::Cell)` across all `sz.bytes` inside bytes
and outside, with `Protected::No`. -/
theorem reborrowSettings_shared_cell {Provenance : Type}
    (vtableLookup : Gen.ThinPointer Provenance → Interp Gen.VTable)
    (ptr : Gen.Pointer Provenance) (sz : Size) (al : Align)
    (params : Gen.TreeBorrowsParams) (fnImplicitWrites : Bool) :
    ReborrowSettings.new vtableLookup ptr
      (.Ref .Immutable {
        layout := .Sized sz al
        inhabited := true
        unsafe_cells := .Sized [(⟨0⟩, sz)]
        freeze := false
        unpin := true
      })
      false params fnImplicitWrites =
      .ok (some {
        inside := List.replicate sz.bytes (.Unprot .Cell)
        outside := .Unprot .Cell
        «protected» := .No
      }) := by
  have hmask : UnsafeCellStrategy.freeze_mask vtableLookup (.Sized [(⟨0⟩, sz)]) (.Sized sz al) ptr.metadata =
      .ok (List.replicate sz.bytes false) := cellsToFreezeMask_single_full sz
  have hmap : (List.replicate sz.bytes false).mapM
      (fun freeze => ReborrowSettings.perm
        (.Ref .Immutable { layout := .Sized sz al, inhabited := true, unsafe_cells := .Sized [(⟨0⟩, sz)], freeze := false, unpin := true })
        .No false true freeze) =
      .ok (List.replicate sz.bytes (.Unprot .Cell)) :=
    mapM_replicate_ok sz.bytes false _ (Gen.Permission.Unprot .Cell) rfl
  simp only [ReborrowSettings.new, PtrType.safe_pointee, Protected.yes,
    Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false, decide_false, Bool.false_and,
    hmask, ok_bind, hmap]
  rfl

/-- `ReborrowSettings::new` on a raw pointer type `PtrType::Raw` returns `None`
because raw pointers do not reborrow in Tree Borrows (`safe_pointee` is `None`). -/
theorem reborrowSettings_raw_none {Provenance : Type}
    (vtableLookup : Gen.ThinPointer Provenance → Interp Gen.VTable)
    (ptr : Gen.Pointer Provenance) (metaKind : Gen.PointerMetaKind) (fnEntry : Bool)
    (params : Gen.TreeBorrowsParams) (fnImplicitWrites : Bool) :
    ReborrowSettings.new vtableLookup ptr (.Raw metaKind) fnEntry params fnImplicitWrites =
      .ok none := rfl

/-- Anneal's read of `copy (*p).rest` when `p` holds a pointer whose tag names
a usable (not `Disabled`) entry with an initialized target and no thin-pointer
element resolution (`needsThinPtrElemResolution = false`, e.g. at offset `0` on
a `ptrTargetSpec` target): the target's value at the entry's projection
followed by `rest`. -/
theorem evalOperand_copy_deref (locals : List LocalSlot) (p : Nat) (rest : List ProjectionElem)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (layouts : Layout.LayoutTable) (callerLocals : List LocalSlot)
    (ptrVal : ProvenancePtr) (sz : Nat) (hp : locals[p]? = some (.init (.ptr ptrVal sz)))
    (entry : BorrowEntry) (he : lookupBorrow borrows ptrVal.tag = some entry)
    (hperm : entry.perm ≠ .disabled)
    (hthin : needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes = false)
    (rootVal : Value) (ht : locals[entry.targetLocal]? = some (.init rootVal)) (v : Value)
    (hr : readProjectedValue locals rootVal (appendProjections entry.targetProjection rest) =
      .ok v) :
    evalOperand locals (.copy ⟨p, .deref :: rest⟩) borrows globals layouts callerLocals =
      .ok v locals := by
  cases htp : entry.targetProjection with
  | nil =>
    rw [htp] at hr
    simp only [appendProjections] at hr
    cases hpe : entry.perm with
    | disabled => exact absurd hpe hperm
    | _ => simp [evalOperand, get?, hp, he, hpe, ht, htp, hr]
  | cons ph pt =>
    rw [htp] at hr hthin
    simp only [appendProjections] at hr
    cases hpe : entry.perm with
    | disabled => exact absurd hpe hperm
    | _ => simp [evalOperand, get?, hp, he, hpe, ht, htp, hr, hthin]

/-- Anneal's read through a pointer whose entry is `Disabled` (by a direct write
to its target or by a write through another pointer) is UB. MiniRust's
`BasicMemory` has no aliasing model and reads the target's current bytes. -/
theorem evalOperand_copy_deref_disabled (locals : List LocalSlot) (p : Nat)
    (rest : List ProjectionElem) (borrows : List BorrowEntry)
    (globals : List MirAst.CapturedAllocation) (layouts : Layout.LayoutTable)
    (callerLocals : List LocalSlot) (ptrVal : ProvenancePtr) (sz : Nat)
    (hp : locals[p]? = some (.init (.ptr ptrVal sz))) (entry : BorrowEntry)
    (he : lookupBorrow borrows ptrVal.tag = some entry) (hperm : entry.perm = .disabled) :
    evalOperand locals (.copy ⟨p, .deref :: rest⟩) borrows globals layouts callerLocals = .ub := by
  simp [evalOperand, get?, hp, he, hperm]

/-- Anneal's write through a pointer whose entry is `Frozen` (a `&raw const`
pointer, also after a `PtrToPtr` cast to `*mut`) is UB. MiniRust's
`BasicMemory` accepts the store. -/
theorem writePlaceValue_deref_frozen (locals : List LocalSlot) (borrows : List BorrowEntry)
    (p : Nat) (rest : List ProjectionElem) (val : Value) (ptrVal : ProvenancePtr) (sz : Nat)
    (hp : locals[p]? = some (.init (.ptr ptrVal sz))) (entry : BorrowEntry)
    (he : lookupBorrow borrows ptrVal.tag = some entry) (hperm : entry.perm = .frozen) :
    writePlaceValue locals borrows ⟨p, .deref :: rest⟩ val = .ub := by
  simp [writePlaceValue, get?, hp, he, hperm]

/-- Anneal's write `(*p) = val` through an `Active` or `Reserved` entry whose
target is the whole local `entry.targetLocal` (no projection): the target local
now holds `val`, wherever the pointer points. -/
theorem writePlaceValue_deref_root (locals : List LocalSlot) (borrows : List BorrowEntry)
    (p : Nat) (val : Value) (ptrVal : ProvenancePtr) (sz : Nat)
    (hp : locals[p]? = some (.init (.ptr ptrVal sz))) (entry : BorrowEntry)
    (he : lookupBorrow borrows ptrVal.tag = some entry)
    (hperm : entry.perm = .active ∨ entry.perm = .reserved)
    (hproj : entry.targetProjection = []) (slot : LocalSlot)
    (ht : locals[entry.targetLocal]? = some slot) (hlive : slot ≠ .dead) :
    writePlaceValue locals borrows ⟨p, [.deref]⟩ val =
      .ok (locals.set entry.targetLocal (.init val)) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp ht
  rcases hperm with hperm | hperm <;>
  (cases slot with
  | dead => exact absurd rfl hlive
  | uninit => simp [writePlaceValue, get?, hp, he, hperm, hproj, set?, hlt, hget]
  | init v => simp [writePlaceValue, get?, hp, he, hperm, hproj, set?, hlt, hget])

/-- Anneal's `Offset(p, n)` (`evalPtrOffsetBinOp`, unstable `b076d6a3`): UB on
a `.disabled` tag; otherwise the 8-byte count `n` is scaled by the pointee's
element stride (`pointeeElemByteStride`) and bounds-checked against the
pointer's allocation (`ptrAllocByteBound?`, `evalBinOpOffset`). MiniRust
(through `minimize`) offsets by `n * size_of::<T>()` bytes with
`ptr_offset_inbounds`. -/
theorem evalRvalue_offset (locals : List LocalSlot) (l r : Operand) (mem : MirSemantics.Memory)
    (decls : List LocalDecl) (layouts : Layout.LayoutTable) (ptrVal : ProvenancePtr) (sz : Nat)
    (locals₁ : List LocalSlot)
    (hl : evalOperand locals l mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.ptr ptrVal sz) locals₁)
    (sc : ScalarInt) (locals₂ : List LocalSlot)
    (hr : evalOperand locals₁ r mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.scalar sc) locals₂) :
    evalRvalue locals (.binaryOp .offset l r) mem decls layouts =
      MirSemantics.evalPtrOffsetBinOp locals₂ mem decls layouts l ptrVal sz sc := by
  simp only [evalRvalue, hl, hr]

/-- Anneal's `PtrToPtr` cast between thin raw pointers to integers keeps the
pointer, tag and offset included (no array-to-element derivation applies);
`minimize` translates a cast between thin raw pointers to its operand. -/
theorem evalRvalue_ptrToPtr (locals : List LocalSlot) (op : Operand) (ty : Ty)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (ptrVal : ProvenancePtr) (locals' : List LocalSlot)
    (h : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.ptr ptrVal 8) locals')
    {dstMutbl : MirAst.Mutability} {dstIt : Gen.IntType}
    (hdst : rawPtrPointeeOf ty = some (dstMutbl, dstIt))
    (hsrc : ∀ srcTy, MirSemantics.operandTy decls layouts op = some srcTy →
      (ptrPointeeOf srcTy).isSome = true)
    (hptr8 : MirSemantics.layoutPointerBytes layouts = 8 := by rfl) :
    evalRvalue locals (.cast .ptrToPtr op ty) mem decls layouts = .ok (.ptr ptrVal 8) locals' mem := by
  have hkind : ∃ elem, ty.kind = .rawPtr dstMutbl elem ∧ (intTyBytes elem).isSome = true := by
    unfold rawPtrPointeeOf at hdst
    cases hk : ty.kind with
    | rawPtr m elem =>
      rw [hk] at hdst
      obtain ⟨⟨sg, n⟩, hb, heq⟩ := Option.map_eq_some_iff.mp hdst
      injection heq with hm _
      exact ⟨elem, by rw [hm], by simp [hb]⟩
    | _ => rw [hk] at hdst; cases hdst
  obtain ⟨elem, hk, hint⟩ := hkind
  cases hty : MirSemantics.operandTy decls layouts op with
  | none =>
    cases elem <;>
      simp_all [evalRvalue, MirSemantics.evalCastPtrToPtr, MirSemantics.thinRawPtrPointee?,
        MirSemantics.arrayPtrOrRefElemLen?, intTyBytes]
  | some srcTy =>
    have hs := hsrc srcTy hty
    rcases srcTy with ⟨sk, sl⟩
    cases sk <;> simp [ptrPointeeOf] at hs
    all_goals
      rename_i m' inner
      cases inner <;> simp [intTyBytes] at hs <;>
        cases elem <;>
          simp_all [evalRvalue, MirSemantics.evalCastPtrToPtr, MirSemantics.thinRawPtrPointee?,
            MirSemantics.arrayPtrOrRefElemLen?, intTyBytes]

/-- Anneal's `PointerExposeProvenance` cast (`p as usize`, `p.expose_provenance()`)
on an 8-byte pointer `ptrVal` whose canonical address `ptrAddress?` is `fullAddr`
(`< 2^64`) records `ptrVal.allocId` in `mem.exposedAllocIds` and returns
`.scalar ⟨fullAddr, 8⟩`. -/
theorem evalRvalue_expose (locals : List LocalSlot) (op : Operand) (ty : Ty)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (ptrVal : ProvenancePtr) (locals' : List LocalSlot) (fullAddr : Nat)
    (h : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.ptr ptrVal 8) locals')
    (hty : MirSemantics.exposeTargetBytes? 8 ty = some 8)
    (hsrc : MirSemantics.isExposePtrSourceTy (MirSemantics.operandTy decls layouts op) = true)
    (haddr : MirSemantics.ptrAddress? locals' mem.borrows mem.callerLocals decls layouts 8 ptrVal
      mem.callStack = some fullAddr)
    (hlt : fullAddr < 2 ^ 64)
    (hptr8 : MirSemantics.layoutPointerBytes layouts = 8 := by rfl) :
    evalRvalue locals (.cast .pointerExposeProvenance op ty) mem decls layouts =
      .ok (.scalar ⟨fullAddr, 8⟩) locals'
        { mem with exposedAllocIds := MirSemantics.recordExposedAllocId mem.exposedAllocIds ptrVal.allocId } := by
  have hwrap : MirSemantics.wrapScalarBits fullAddr (MirSemantics.scalarModulus 8) = fullAddr := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hlt]
  dsimp only [evalRvalue, MirSemantics.evalPointerExposeProvenance]
  rw [hptr8, hsrc]
  simp [hty, h, haddr, hwrap]

/-- Anneal's `PointerWithExposedProvenance` cast (`n as *const T`,
`ptr::with_exposed_provenance(n)`) on an 8-byte unsigned `usize` scalar `sc`
(`sc.bits < 2^64`) recovers the exposed pointer `recoveredVal` via
`recoverExposedPtrValue?`. -/
theorem evalRvalue_withExposed (locals : List LocalSlot) (op : Operand) (ty : Ty)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (sc : ScalarInt) (locals' : List LocalSlot) (recoveredVal : Value)
    (h : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.scalar sc) locals')
    (hsz : sc.sizeBytes = 8)
    (hlt : sc.bits < 2 ^ 64)
    (hbad : MirSemantics.isBadWithExposedTargetTy ty = false)
    (hsrc : MirSemantics.isExposeIntSourceTy 8 (MirSemantics.operandTy decls layouts op) = true)
    (hsigned : MirSemantics.operandIsSigned decls op layouts = false)
    (hrec : MirSemantics.recoverExposedPtrValue? locals' mem.borrows mem.globals mem.callerLocals
      mem.exposedAllocIds decls layouts 8 sc.bits mem.callStack = some recoveredVal)
    (hptr8 : MirSemantics.layoutPointerBytes layouts = 8 := by rfl) :
    evalRvalue locals (.cast .pointerWithExposedProvenance op ty) mem decls layouts =
      .ok recoveredVal locals' mem := by
  have hwrap : MirSemantics.wrapScalarBits sc.bits (MirSemantics.scalarModulus 8) = sc.bits := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hlt]
  dsimp only [evalRvalue, MirSemantics.evalPointerWithExposedProvenance]
  rw [hptr8, hbad, hsrc, h]
  dsimp only
  rw [hsz, hsigned]
  simp [hwrap, hrec]

/-! ## MiniRust: thin-pointer loads, stores, and zero-offset arithmetic -/

theorem decode_thinRawPtr_uninit : Type.decode thinRawPtrTy (uninitBytes usizeIt) = .ok none := rfl

theorem typedLoad_of_ok {m : Mach} {ptr : Ptr} {ty : Gen.Type} {sz : Size} {al : Align}
    {align : Align} {bytes : List Byte} {cm : Gen.ConcurrentMemory BM} {val : Val}
    (hlay : Type.layout ty = .ok (.Sized sz al))
    (hload : CM.load m.mem ptr sz align .None = .ok (bytes, cm))
    (hdec : Type.decode ty bytes = .ok (some val))
    (hck : checkValue (m := some { m with mem := cm }) val ty = .ok ()) :
    typedLoad m ptr ty align .None = .ok (val, { m with mem := cm }) := by
  simp only [typedLoad, hlay, expect_size_sized, ok_bind, hload, hdec, hck, pure_ok]

theorem typedStore_of_ok {m : Mach} {ptr : Ptr} {val : Val} {ty : Gen.Type}
    {align : Align} {bytes : List Byte} {cm : Gen.ConcurrentMemory BM}
    (hck : checkValue (m := some m) val ty = .ok ())
    (henc : Type.encode ty val = .ok bytes)
    (hstore : CM.store m.mem ptr bytes align .None = .ok cm) :
    typedStore m ptr val ty align .None = .ok { m with mem := cm } := by
  simp only [typedStore, hck, ok_bind, pure_ok, henc, hstore]

theorem cm_dereferenceable_offsetPtr {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A)
    (p : Ptr) (allocId : Nat) (hp : p.provenance = some (⟨(allocId : Int)⟩, ()))
    (it : Gen.IntType) (data : List Byte)
    (hA : A[allocId]? = some (stackAlloc p.addr it data))
    (relOff : Nat) (sz : Size) (hbound : relOff + sz.bytes ≤ data.length) :
    CM.dereferenceable m.mem (offsetPtr p relOff) sz = .ok () := by
  have hchk : ¬ ((data.length : Int) < (relOff : Int) + (sz.bytes : Int)) := by
    exact_mod_cast Nat.not_lt.mpr hbound
  simp only [CM.dereferenceable, BM.dereferenceable, BM.check_ptr, offsetPtr, hp,
    listIndex, h.allocs]
  split
  · rfl
  · simp [hA, stackAlloc, Allocation.size, hchk]

theorem cm_dereferenceable_of_shape_eq {m1 m2 : Mach} {ctx : Ctx} {frames1 frames2 : List Frame}
    {A : List Gen.Allocation} (h1 : Shape m1 ctx frames1 A) (h2 : Shape m2 ctx frames2 A)
    (ptr : Ptr) (sz : Size) :
    CM.dereferenceable m1.mem ptr sz = CM.dereferenceable m2.mem ptr sz := by
  simp only [CM.dereferenceable, BM.dereferenceable, BM.check_ptr, listIndex, h1.allocs, h2.allocs]

theorem cm_load_local_8 {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat)
    (data : List Byte)
    (hL : L[i]? = some (localAlloc ctx i usizeIt data)) (hlen : data.length = 8)
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    CM.load m.mem (localPtr ctx i) ⟨8⟩ align .None =
      .ok (data, (withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD i 0, ⟨8⟩⟩).mem) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hset := set_self_of_getElem? L i _ hL
  have htk : data.take 8 = data := List.take_of_length_le (by omega)
  simp only [CM.load, BM.load, hal, BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset, htk, withMem]

theorem cm_store_local_8 {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat)
    (oldData newData : List Byte)
    (hL : L[i]? = some (localAlloc ctx i usizeIt oldData))
    (hold : oldData.length = 8) (hnew : newData.length = 8)
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    CM.store m.mem (localPtr ctx i) newData align .None =
      .ok (withMem m (ctx.base ++ L.set i (localAlloc ctx i usizeIt newData))
            ⟨.Store, .None, ctx.addrs.getD i 0, ⟨8⟩⟩).mem := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hdrop : oldData.drop 8 = [] := List.drop_eq_nil_of_le (by omega)
  simp only [CM.store, BM.store, hal, BM.check_ptr, hnew, localPtr, listIndex, h.allocs]
  simp [hi, hLi, Allocation.size, hold, hnew, writeSubsliceAtIndex, listSet, withMem, hdrop]
  simp [localAlloc, stackAlloc, usizeIt]

theorem typedLoad_local_thinRawPtr {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat)
    (tAddr : Nat) (htlt : tAddr < 2 ^ 64) (tProv : Option Prov)
    (hL : L[i]? = some (localAlloc ctx i usizeIt (ptrBytes tAddr tProv)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) thinRawPtrTy align .None =
        .ok (.Ptr { thin_pointer := { addr := tAddr, provenance := tProv }, metadata := none }, m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  have hload := cm_load_local_8 h i (ptrBytes tAddr tProv) hL (ptrBytes_length tAddr tProv) align hal
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD i 0, ⟨8⟩⟩, ?_,
    withMem_shape h _⟩
  exact typedLoad_of_ok layout_thinRawPtr hload (decode_thinRawPtr tAddr htlt tProv)
    (checkValue_thinRawPtr tAddr htlt tProv)

theorem typedLoad_local_thinRawPtr_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat)
    (hL : L[i]? = some (localAlloc ctx i usizeIt (uninitBytes usizeIt)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) thinRawPtrTy align .None = .error (.ub msg) := by
  have hload := cm_load_local_8 h i (uninitBytes usizeIt) hL rfl align hal
  refine ⟨"load at type but the data in memory violates the language invariant", ?_⟩
  simp only [typedLoad, layout_thinRawPtr, expect_size_sized, ok_bind, hload,
    decode_thinRawPtr_uninit, ub]

theorem typedStore_local_thinRawPtr {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat)
    (data : List Byte) (tAddr : Nat) (htlt : tAddr < 2 ^ 64) (tProv : Option Prov)
    (hL : L[i]? = some (localAlloc ctx i usizeIt data)) (hlen : data.length = 8)
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    typedStore m (localPtr ctx i)
        (.Ptr { thin_pointer := { addr := tAddr, provenance := tProv }, metadata := none })
        thinRawPtrTy align .None =
      .ok (withMem m (ctx.base ++ L.set i (localAlloc ctx i usizeIt (ptrBytes tAddr tProv)))
            ⟨.Store, .None, ctx.addrs.getD i 0, ⟨8⟩⟩) := by
  have hstore := cm_store_local_8 h i data (ptrBytes tAddr tProv) hL hlen
    (ptrBytes_length tAddr tProv) align hal
  exact typedStore_of_ok (checkValue_thinRawPtr tAddr htlt tProv)
    (encode_thinRawPtr tAddr htlt tProv) hstore

theorem typedLoad_ptr_thinRawPtr {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (tAddr : Nat) (htlt : tAddr < 2 ^ 64)
    (tProv : Option Prov)
    (hA : A[k]? = some (stackAlloc p.addr usizeIt (ptrBytes tAddr tProv))) :
    ∃ m', typedLoad m p thinRawPtrTy ⟨1⟩ .None =
        .ok (.Ptr { thin_pointer := { addr := tAddr, provenance := tProv }, metadata := none }, m') ∧
      Shape m' ctx frames A := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨m', hm', hs⟩ := typedLoad_local_thinRawPtr (h.toFocus k p.addr) 0 tAddr htlt tProv
    (focusCtx_drop_get hA) ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp] at hm'
  rw [focusCtx_append] at hs
  exact ⟨m', hm', hs.ofFocus⟩

theorem typedLoad_ptr_thinRawPtr_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ()))
    (hA : A[k]? = some (stackAlloc p.addr usizeIt (uninitBytes usizeIt))) :
    ∃ msg, typedLoad m p thinRawPtrTy ⟨1⟩ .None = .error (.ub msg) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨msg, hmsg⟩ := typedLoad_local_thinRawPtr_uninit (h.toFocus k p.addr) 0
    (focusCtx_drop_get hA) ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp] at hmsg
  exact ⟨msg, hmsg⟩

theorem typedStore_ptr_thinRawPtr {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (data : List Byte)
    (tAddr : Nat) (htlt : tAddr < 2 ^ 64) (tProv : Option Prov)
    (hA : A[k]? = some (stackAlloc p.addr usizeIt data)) (hlen : data.length = 8) :
    typedStore m p
        (.Ptr { thin_pointer := { addr := tAddr, provenance := tProv }, metadata := none })
        thinRawPtrTy ⟨1⟩ .None =
      .ok (withMem m (A.set k (stackAlloc p.addr usizeIt (ptrBytes tAddr tProv)))
            ⟨.Store, .None, p.addr, ⟨8⟩⟩) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  have hst := typedStore_local_thinRawPtr (h.toFocus k p.addr) 0 data tAddr htlt tProv
    (focusCtx_drop_get hA) hlen ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp, focusCtx_localAlloc,
    focusCtx_set ctx A k p.addr hk] at hst
  exact hst

theorem typedLoad_local_declPtrTy {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat)
    (t : MirAst.Ty) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (hp_ty : ptrPointeeOf t = some (mutbl, pointeeIt))
    (hgood : GoodSize pointeeIt.size.bytes)
    (tAddr : Nat) (htpos : 0 < tAddr) (htlt : tAddr < 2 ^ 64) (tProv : Option Prov)
    (htal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (tAddr : Int) = true)
    (htderef : CM.dereferenceable m.mem { addr := (tAddr : Int), provenance := tProv } pointeeIt.size = .ok ())
    (hL : L[i]? = some (localAlloc ctx i usizeIt (ptrBytes tAddr tProv)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) (declPtrTy t) align .None =
        .ok (.Ptr { thin_pointer := { addr := tAddr, provenance := tProv }, metadata := none }, m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  have hload := cm_load_local_8 h i (ptrBytes tAddr tProv) hL (ptrBytes_length tAddr tProv) align hal
  let m' := withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD i 0, ⟨8⟩⟩
  have hs' : Shape m' ctx frames (ctx.base ++ L) := withMem_shape h _
  have htderef' : CM.dereferenceable m'.mem { addr := (tAddr : Int), provenance := tProv } pointeeIt.size = .ok () := by
    rw [cm_dereferenceable_of_shape_eq hs' h]
    exact htderef
  refine ⟨m', ?_, hs'⟩
  exact typedLoad_of_ok (layout_declPtrTy t) hload (decode_declPtrTy t tAddr htlt tProv)
    (checkValue_declPtrTy hp_ty m' hgood tAddr htpos htlt tProv htal htderef')

theorem typedLoad_local_declPtrTy_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat)
    (t : MirAst.Ty)
    (hL : L[i]? = some (localAlloc ctx i usizeIt (uninitBytes usizeIt)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) (declPtrTy t) align .None = .error (.ub msg) := by
  have hload := cm_load_local_8 h i (uninitBytes usizeIt) hL rfl align hal
  refine ⟨"load at type but the data in memory violates the language invariant", ?_⟩
  simp only [typedLoad, layout_declPtrTy t, expect_size_sized, ok_bind, hload,
    decode_declPtrTy_uninit t, ub]

theorem typedStore_local_declPtrTy {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat)
    (t : MirAst.Ty) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (hp_ty : ptrPointeeOf t = some (mutbl, pointeeIt))
    (hgood : GoodSize pointeeIt.size.bytes)
    (data : List Byte) (tAddr : Nat) (htpos : 0 < tAddr) (htlt : tAddr < 2 ^ 64) (tProv : Option Prov)
    (htal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (tAddr : Int) = true)
    (htderef : CM.dereferenceable m.mem { addr := (tAddr : Int), provenance := tProv } pointeeIt.size = .ok ())
    (hL : L[i]? = some (localAlloc ctx i usizeIt data)) (hlen : data.length = 8)
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    typedStore m (localPtr ctx i)
        (.Ptr { thin_pointer := { addr := tAddr, provenance := tProv }, metadata := none })
        (declPtrTy t) align .None =
      .ok (withMem m (ctx.base ++ L.set i (localAlloc ctx i usizeIt (ptrBytes tAddr tProv)))
            ⟨.Store, .None, ctx.addrs.getD i 0, ⟨8⟩⟩) := by
  have hstore := cm_store_local_8 h i data (ptrBytes tAddr tProv) hL hlen
    (ptrBytes_length tAddr tProv) align hal
  exact typedStore_of_ok (checkValue_declPtrTy hp_ty m hgood tAddr htpos htlt tProv htal htderef)
    (encode_declPtrTy t tAddr htlt tProv) hstore

theorem typedLoad_ptr_declPtrTy {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ()))
    (t : MirAst.Ty) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (hp_ty : ptrPointeeOf t = some (mutbl, pointeeIt))
    (hgood : GoodSize pointeeIt.size.bytes)
    (tAddr : Nat) (htpos : 0 < tAddr) (htlt : tAddr < 2 ^ 64) (tProv : Option Prov)
    (htal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (tAddr : Int) = true)
    (htderef : CM.dereferenceable m.mem { addr := (tAddr : Int), provenance := tProv } pointeeIt.size = .ok ())
    (hA : A[k]? = some (stackAlloc p.addr usizeIt (ptrBytes tAddr tProv))) :
    ∃ m', typedLoad m p (declPtrTy t) ⟨1⟩ .None =
        .ok (.Ptr { thin_pointer := { addr := tAddr, provenance := tProv }, metadata := none }, m') ∧
      Shape m' ctx frames A := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨m', hm', hs⟩ := typedLoad_local_declPtrTy (h.toFocus k p.addr) 0 t mutbl pointeeIt
    hp_ty hgood tAddr htpos htlt tProv htal htderef (focusCtx_drop_get hA) ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp] at hm'
  rw [focusCtx_append] at hs
  exact ⟨m', hm', hs.ofFocus⟩

theorem typedLoad_ptr_declPtrTy_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ())) (t : MirAst.Ty)
    (hA : A[k]? = some (stackAlloc p.addr usizeIt (uninitBytes usizeIt))) :
    ∃ msg, typedLoad m p (declPtrTy t) ⟨1⟩ .None = .error (.ub msg) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨msg, hmsg⟩ := typedLoad_local_declPtrTy_uninit (h.toFocus k p.addr) 0 t
    (focusCtx_drop_get hA) ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp] at hmsg
  exact ⟨msg, hmsg⟩

theorem typedStore_ptr_declPtrTy {m : Mach} {ctx : Ctx} {frames : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx frames A) (p : Ptr) (k : Nat)
    (hp : p.provenance = some (⟨(k : Int)⟩, ()))
    (t : MirAst.Ty) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (hp_ty : ptrPointeeOf t = some (mutbl, pointeeIt))
    (hgood : GoodSize pointeeIt.size.bytes)
    (data : List Byte)
    (tAddr : Nat) (htpos : 0 < tAddr) (htlt : tAddr < 2 ^ 64) (tProv : Option Prov)
    (htal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (tAddr : Int) = true)
    (htderef : CM.dereferenceable m.mem { addr := (tAddr : Int), provenance := tProv } pointeeIt.size = .ok ())
    (hA : A[k]? = some (stackAlloc p.addr usizeIt data)) (hlen : data.length = 8) :
    typedStore m p
        (.Ptr { thin_pointer := { addr := tAddr, provenance := tProv }, metadata := none })
        (declPtrTy t) ⟨1⟩ .None =
      .ok (withMem m (A.set k (stackAlloc p.addr usizeIt (ptrBytes tAddr tProv)))
            ⟨.Store, .None, p.addr, ⟨8⟩⟩) := by
  have hk : k < A.length := (List.getElem?_eq_some_iff.mp hA).1
  have hst := typedStore_local_declPtrTy (h.toFocus k p.addr) 0 t mutbl pointeeIt
    hp_ty hgood data tAddr htpos htlt tProv htal htderef (focusCtx_drop_get hA) hlen ⟨1⟩ (isAligned_one _)
  rw [focusCtx_localPtr ctx A k (Nat.le_of_lt hk) p hp, focusCtx_localAlloc,
    focusCtx_set ctx A k p.addr hk] at hst
  exact hst

theorem retagPtrBM_shape {m : Mach} {ctx : Ctx} {f1 f2 : Frame} {rest : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx (f1 :: f2 :: rest) A) (ptr : Gen.Pointer Prov) :
    retagPtrBM m ptr = .ok ptr := by
  simp [retagPtrBM, listIndex, h.threads, h.active, thread1]

/-- `Machine::retag_val` on a pointer or safe reference value in `BasicMemory`:
delegates to `retagPtrBM` and returns the pointer unchanged. -/
theorem retagVal_ptr_shape {m : Mach} {ctx : Ctx} {f1 f2 : Frame} {rest : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx (f1 :: f2 :: rest) A)
    (fnEntry : Bool) (ptr : Gen.Pointer Prov) (ptrTy : Gen.PtrType) :
    retagVal m fnEntry (.Ptr ptr) (.Ptr ptrTy) = .ok (.Ptr ptr) := by
  simp [retagVal, retagPtrBM_shape h ptr]

/-- `Statement::Validate` on a place holding a valid thin raw pointer or safe
reference (`declPtrTy t`): loads and validates the pointer against `m.mem`,
runs `retag_val` (`retagPtrBM`), and stores the identical pointer bytes back,
preserving `Shape`. -/
theorem evalStatement_validate_declPtrTy {m : Mach} {ctx : Ctx} {f1 f2 : Frame}
    {rest : List Frame} {A : List Gen.Allocation}
    (h : Shape m ctx (f1 :: f2 :: rest) A)
    (pe : Gen.PlaceExpr) (p : Ptr) (k : Nat) (fnEntry : Bool)
    (hp : p.provenance = some (⟨(k : Int)⟩, ()))
    (t : MirAst.Ty) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (hp_ty : ptrPointeeOf t = some (mutbl, pointeeIt))
    (hgood : GoodSize pointeeIt.size.bytes)
    (tAddr : Nat) (htpos : 0 < tAddr) (htlt : tAddr < 2 ^ 64) (tProv : Option Prov)
    (htal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (tAddr : Int) = true)
    (htderef : CM.dereferenceable m.mem { addr := (tAddr : Int), provenance := tProv } pointeeIt.size = .ok ())
    (hpe : evalPlace m pe =
      .ok (({ ptr := { thin_pointer := p, metadata := none }, aligned := true }, declPtrTy t), m))
    (hA : A[k]? = some (stackAlloc p.addr usizeIt (ptrBytes tAddr tProv))) :
    ∃ m', evalStatement m (.Validate pe fnEntry) = .ok m' ∧
      Shape m' ctx (f1 :: f2 :: rest) A := by
  obtain ⟨m1, hload, hs1⟩ := typedLoad_ptr_declPtrTy h p k hp t mutbl pointeeIt
    hp_ty hgood tAddr htpos htlt tProv htal htderef hA
  have hrt : retagVal m1 fnEntry
      (.Ptr { thin_pointer := { addr := tAddr, provenance := tProv }, metadata := none })
      (declPtrTy t) =
      .ok (.Ptr { thin_pointer := { addr := tAddr, provenance := tProv }, metadata := none }) := by
    rcases declPtrTy_cases t with hty | ⟨_, _, _, hty⟩ <;>
      rw [hty] <;>
      exact retagVal_ptr_shape hs1 fnEntry _ _
  have htderef1 : CM.dereferenceable m1.mem { addr := (tAddr : Int), provenance := tProv } pointeeIt.size = .ok () := by
    rw [cm_dereferenceable_of_shape_eq hs1 h]
    exact htderef
  have hstore := typedStore_ptr_declPtrTy hs1 p k hp t mutbl pointeeIt hp_ty hgood
    (ptrBytes tAddr tProv) tAddr htpos htlt tProv htal htderef1 hA (ptrBytes_length tAddr tProv)
  have hset : A.set k (stackAlloc p.addr usizeIt (ptrBytes tAddr tProv)) = A :=
    set_self_of_getElem? A k _ hA
  rw [hset] at hstore
  refine ⟨withMem m1 A ⟨.Store, .None, p.addr, ⟨8⟩⟩, ?_, withMem_shape hs1 _⟩
  simp only [evalStatement, hpe, ok_bind, placeLoad, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, hload, hrt, placeStore, hstore]

theorem ptrOffsetInbounds_zero (m : Mach) (ptr : Ptr)
    (haddr0 : 0 ≤ ptr.addr) (haddrMax : ptr.addr < 2 ^ 64) :
    ptrOffsetInbounds m ptr 0 = .ok ptr := by
  have hderef : CM.signed_dereferenceable m.mem ptr 0 = .ok () := by
    simp [CM.signed_dereferenceable, BM.signed_dereferenceable, BM.dereferenceable, BM.check_ptr]
  have hb1 : inBounds 0 .Signed x86_64.PTR_SIZE = true := by decide
  have h2 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  have hmax : ptr.addr < 18446744073709551616 := h2 ▸ haddrMax
  have hb2 : inBounds ptr.addr .Unsigned x86_64.PTR_SIZE = true := by
    rw [inBounds_usize]
    simp [haddr0, hmax]
  unfold ptrOffsetInbounds
  rw [hderef, ok_bind]
  cases ptr
  simp [hb1, hb2]

/-! ## Anneal: Tree Borrows preservation under `ptrAliasingOk` -/

theorem projectionsOverlap_nil_right (proj : List ProjectionElem) :
    MirSemantics.projectionsOverlap proj [] = true := by
  unfold MirSemantics.projectionsOverlap
  have h0 : MirSemantics.normalizeSubsliceProjections
      (MirSemantics.stripTransparentProjections []) = [] := rfl
  rw [h0]
  cases MirSemantics.normalizeSubsliceProjections (MirSemantics.stripTransparentProjections proj) <;>
    rfl

private def isNonTransparentProj : ProjectionElem → Bool
  | .opaqueCast _ | .unwrapUnsafeBinder _ => false
  | _ => true

private theorem stripTransparentProjections_nonTransparent (projs : List ProjectionElem) :
    ∀ e ∈ MirSemantics.stripTransparentProjections projs, isNonTransparentProj e = true := by
  induction projs with
  | nil => intro _ h; cases h
  | cons p rest ih =>
    cases p <;> simp only [MirSemantics.stripTransparentProjections]
    all_goals
      first
      | exact ih
      | exact fun e he => (List.mem_cons.mp he).elim (fun h => h ▸ rfl) (ih e)

theorem borrowProjSteps_stripTransparent (projs : List ProjectionElem) :
    borrowProjSteps (MirSemantics.stripTransparentProjections projs) = borrowProjSteps projs := by
  induction projs with
  | nil => rfl
  | cons p rest ih =>
    cases p <;> simp [MirSemantics.stripTransparentProjections, borrowProjSteps, ih]

private theorem borrowProjOverlap_stripped {a b : List ProjectionElem}
    (ha : ∀ e ∈ a, isNonTransparentProj e = true)
    (hb : ∀ e ∈ b, isNonTransparentProj e = true)
    (hst : borrowProjOverlap (borrowProjSteps a) (borrowProjSteps b) = false) :
    MirSemantics.projectionsOverlapAux (MirSemantics.normalizeSubsliceProjectionsAux .none a)
      (MirSemantics.normalizeSubsliceProjectionsAux .none b) = false := by
  induction a generalizing b with
  | nil => simp [borrowProjSteps, borrowProjOverlap] at hst
  | cons ea ra ih =>
    have hea : isNonTransparentProj ea = true := ha ea (.head _)
    have hra : ∀ e ∈ ra, isNonTransparentProj e = true := fun e h => ha e (.tail _ h)
    cases b with
    | nil =>
      cases ea <;> simp_all [isNonTransparentProj, borrowProjSteps, borrowProjOverlap]
    | cons eb rb =>
      have heb : isNonTransparentProj eb = true := hb eb (.head _)
      have hrb : ∀ e ∈ rb, isNonTransparentProj e = true := fun e h => hb e (.tail _ h)
      cases ea <;> first | (simp [isNonTransparentProj] at hea) | skip
      all_goals
        cases eb <;> first | (simp [isNonTransparentProj] at heb) | skip
      all_goals
        simp only [borrowProjSteps, borrowProjOverlap] at hst
      all_goals first | (simp at hst) | skip
      all_goals simp only [MirSemantics.projectionsOverlapAux]
      · rename_i idxA _ idxB _
        by_cases hidx : idxA = idxB
        · subst hidx
          simp at hst
          simp [Nat.beq_refl, ih hra hrb hst]
        · have hne : Nat.beq idxA idxB = false :=
            Bool.eq_false_iff.mpr (fun h => hidx (Nat.beq_eq.mp h))
          simp [hne]
      · rename_i offA _ feA offB _ feB
        cases feA <;> cases feB
        · by_cases hoff : offA = offB
          · subst hoff
            simp at hst
            simp [Nat.beq_refl, ih hra hrb hst]
          · have hne : Nat.beq offA offB = false :=
              Bool.eq_false_iff.mpr (fun h => hoff (Nat.beq_eq.mp h))
            simp [hne]
        · simp at hst
          simpa using ih hra hrb hst
        · simp at hst
          simpa using ih hra hrb hst
        · by_cases hoff : offA = offB
          · subst hoff
            simp at hst
            simp [Nat.beq_refl, ih hra hrb hst]
          · have hne : Nat.beq offA offB = false :=
              Bool.eq_false_iff.mpr (fun h => hoff (Nat.beq_eq.mp h))
            simp [hne]
      · rename_i _ varA _ varB
        by_cases hvar : varA = varB
        · subst hvar
          simp at hst
          simp [Nat.beq_refl, ih hra hrb hst]
        · have hne : Nat.beq varA varB = false :=
            Bool.eq_false_iff.mpr (fun h => hvar (Nat.beq_eq.mp h))
          simp [hne]

/-- `borrowProjOverlap` on `borrowProjSteps` is a sound static approximation of
Anneal's `MirSemantics.projectionsOverlap`: static disjointness implies dynamic
disjointness. (Since `b076d6a3`, the dynamic check also normalizes nested
`.subslice`s and separates a `.subslice` from an outside `.constantIndex`, which
`borrowProjSteps` conservatively abstracts as `.other`.) -/
theorem borrowProjOverlap_borrowProjSteps {projA projB : List ProjectionElem}
    (h : borrowProjOverlap (borrowProjSteps projA) (borrowProjSteps projB) = false) :
    MirSemantics.projectionsOverlap projA projB = false := by
  unfold MirSemantics.projectionsOverlap MirSemantics.normalizeSubsliceProjections
  rw [← borrowProjSteps_stripTransparent projA, ← borrowProjSteps_stripTransparent projB] at h
  exact borrowProjOverlap_stripped (stripTransparentProjections_nonTransparent projA)
    (stripTransparentProjections_nonTransparent projB) h

theorem updateBorrowPermAtProj_fields (e : BorrowEntry) (targetLocal : Nat)
    (writerTag : Option Nat) (writeProj : List ProjectionElem) (off len : Nat) (d : Nat := 0) :
    (updateBorrowPermAtProj e targetLocal writerTag writeProj off len d).tag = e.tag ∧
    (updateBorrowPermAtProj e targetLocal writerTag writeProj off len d).targetLocal = e.targetLocal ∧
    (updateBorrowPermAtProj e targetLocal writerTag writeProj off len d).targetProjection = e.targetProjection ∧
    (updateBorrowPermAtProj e targetLocal writerTag writeProj off len d).protector = e.protector ∧
    (updateBorrowPermAtProj e targetLocal writerTag writeProj off len d).rangeOffset = e.rangeOffset ∧
    (updateBorrowPermAtProj e targetLocal writerTag writeProj off len d).rangeLen = e.rangeLen := by
  have h := updateBorrowPermAtProj_preserves_fields e targetLocal writerTag writeProj off len d
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem updateBorrowPermAtProj_cases (e : BorrowEntry)
    (targetLocal tag : Nat) (writeProj : List ProjectionElem) (d : Nat := 0) :
    updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 d = e ∨
    ((e.perm = .reserved ∨ e.perm = .reservedFrz true ∨ e.perm = .reservedIM) ∧
      updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 d = { e with perm := .active }) ∨
    updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 d = { e with perm := .disabled } := by
  unfold updateBorrowPermAtProj MirSemantics.treeBorrowWriterRelatedness
  dsimp only []
  rcases e with ⟨_, _, _, perm, _, _, _, _, _, _⟩
  cases Bool.and (Nat.beq _ d) (Nat.beq _ targetLocal)
  · exact .inl rfl
  · dsimp only []
    cases Nat.beq _ tag
    · dsimp only []
      cases borrowEntryOverlapsWrite _ writeProj 0 0
      · exact .inl rfl
      · dsimp only []
        cases perm with
        | cell | reservedIM => exact .inl rfl
        | reservedFrz c => cases c <;> exact .inr (.inr rfl)
        | unique | frozen | disabled => exact .inr (.inr rfl)
    · dsimp only []
      cases perm with
      | reservedFrz c =>
        cases c
        · exact .inr (.inl ⟨.inl rfl, rfl⟩)
        · exact .inr (.inl ⟨.inr (.inl rfl), rfl⟩)
      | reservedIM => exact .inr (.inl ⟨.inr (.inr rfl), rfl⟩)
      | cell | unique | frozen | disabled => exact .inl rfl

theorem updateBorrowPermAtProj_cases_of_ne_reserved {e : BorrowEntry}
    (hnr : e.perm ≠ .reserved ∧ e.perm ≠ .reservedFrz true ∧ e.perm ≠ .reservedIM)
    (targetLocal tag : Nat) (writeProj : List ProjectionElem) (d : Nat := 0) :
    updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 d = e ∨
    updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 d = { e with perm := .disabled } := by
  rcases updateBorrowPermAtProj_cases e targetLocal tag writeProj d with h | ⟨hr | hr | hr, _⟩ | h
  · exact .inl h
  · exact absurd hr hnr.1
  · exact absurd hr hnr.2.1
  · exact absurd hr hnr.2.2
  · exact .inr h

theorem updateBorrowPermAtProj_self_or_disjoint_keep (e : BorrowEntry) (targetLocal tag : Nat)
    (writeProj : List ProjectionElem) (d : Nat := 0)
    (h : e.targetLocal = targetLocal →
      e.tag = tag ∨
      (e.tag ≠ tag ∧ MirSemantics.projectionsOverlap e.targetProjection writeProj = false)) :
    updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 d = e ∨
    updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 d = { e with perm := .active } := by
  rcases e with ⟨etag, etloc, etproj, perm, eroff, erlen, eprot, eptag, etd, ead⟩
  unfold updateBorrowPermAtProj MirSemantics.treeBorrowWriterRelatedness
  cases htd : Nat.beq etd d with
  | false => exact .inl rfl
  | true =>
    cases hloc : Nat.beq etloc targetLocal with
    | false => exact .inl rfl
    | true =>
      dsimp only [Bool.and]
      rcases h (Nat.beq_eq.mp hloc) with heqTag | ⟨hneTag, hdisj⟩
      · have htag : Nat.beq etag tag = true := Nat.beq_eq.mpr heqTag
        simp only [htag]
        cases perm with
        | reservedFrz c => cases c <;> exact .inr rfl
        | reservedIM => exact .inr rfl
        | cell | unique | frozen | disabled => exact .inl rfl
      · have htag : Nat.beq etag tag = false := by
          cases hb : Nat.beq etag tag with
          | false => rfl
          | true => exact False.elim (hneTag (Nat.beq_eq.mp hb))
        have hov : borrowEntryOverlapsWrite ⟨etag, etloc, etproj, perm, eroff, erlen, eprot, eptag, etd, ead⟩ writeProj 0 0 = false := by
          simpa [borrowEntryOverlapsWrite] using hdisj
        simp [htag, hov]

theorem updateBorrowPermAtProj_nil_eq (e : BorrowEntry) (targetLocal : Nat)
    (writerTag : Option Nat) (d : Nat := 0) :
    updateBorrowPermAtProj e targetLocal writerTag [] 0 0 d =
      updateBorrowPerm e targetLocal writerTag d := by
  have hov : borrowEntryOverlapsWrite e [] 0 0 = true := by
    simpa [borrowEntryOverlapsWrite] using projectionsOverlap_nil_right e.targetProjection
  unfold updateBorrowPermAtProj updateBorrowPerm
  rw [hov]
  cases Bool.and (Nat.beq e.targetFrameDepth d) (Nat.beq e.targetLocal targetLocal) <;>
    cases MirSemantics.treeBorrowWriterRelatedness e writerTag <;> rfl

theorem invalidateConflictingBorrows_eq_map (borrows : List BorrowEntry)
    (targetLocal : Nat) (writerTag : Option Nat) (d : Nat := 0) :
    invalidateConflictingBorrows borrows targetLocal writerTag d =
      borrows.map (fun e => updateBorrowPermAtProj e targetLocal writerTag [] 0 0 d) := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    rw [invalidateConflictingBorrows_cons, ← updateBorrowPermAtProj_nil_eq e targetLocal writerTag d, ih]
    rfl

theorem invalidateConflictingBorrowsAtProj_eq_map (borrows : List BorrowEntry)
    (targetLocal : Nat) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (off len : Nat) (d : Nat := 0) :
    invalidateConflictingBorrowsAtProj borrows targetLocal writerTag writeProj off len d =
      borrows.map (fun e => updateBorrowPermAtProj e targetLocal writerTag writeProj off len d) := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    simp [invalidateConflictingBorrowsAtProj, ih]

theorem lookupBorrow_map_eq {borrows : List BorrowEntry} {f : BorrowEntry → BorrowEntry}
    (htag : ∀ e, (f e).tag = e.tag) (tag : Nat) :
    lookupBorrow (borrows.map f) tag = (lookupBorrow borrows tag).map f := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, lookupBorrow, htag e]
    cases Nat.beq e.tag tag
    · exact ih
    · rfl

theorem lookupBorrow_mem_and_tag {borrows : List BorrowEntry} {tag : Nat} {entry : BorrowEntry}
    (h : lookupBorrow borrows tag = some entry) :
    entry ∈ borrows ∧ entry.tag = tag := by
  induction borrows with
  | nil => simp [lookupBorrow] at h
  | cons e rest ih =>
    unfold lookupBorrow at h
    cases hb : Nat.beq e.tag tag with
    | true =>
      rw [hb] at h
      simp at h
      subst h
      exact ⟨.head _, Nat.beq_eq.mp hb⟩
    | false =>
      rw [hb] at h
      obtain ⟨hmem, htag⟩ := ih h
      exact ⟨.tail _ hmem, htag⟩

theorem updateBorrowPerm_self_or_other (e : BorrowEntry) (targetLocal tag : Nat) (d : Nat := 0)
    (h : e.targetLocal = targetLocal →
      e.tag = tag ∧ e.perm ≠ .reserved ∧ e.perm ≠ .reservedFrz true ∧ e.perm ≠ .reservedIM) :
    updateBorrowPerm e targetLocal (some tag) d = e := by
  rcases e with ⟨etag, etloc, etproj, perm, eroff, erlen, eprot, eptag, etd, ead⟩
  unfold updateBorrowPerm MirSemantics.treeBorrowWriterRelatedness
  cases htd : Nat.beq etd d with
  | false => rfl
  | true =>
    cases hloc : Nat.beq etloc targetLocal with
    | false => rfl
    | true =>
      dsimp only [Bool.and]
      obtain ⟨heqTag, hnr1, hnr2, hnr3⟩ := h (Nat.beq_eq.mp hloc)
      have htag : Nat.beq etag tag = true := Nat.beq_eq.mpr heqTag
      simp only [htag]
      cases perm with
      | reservedFrz c =>
        cases c
        · exact absurd rfl hnr1
        · exact absurd rfl hnr2
      | reservedIM => exact absurd rfl hnr3
      | cell | unique | frozen | disabled => rfl

theorem invalidateConflictingBorrows_self (borrows : List BorrowEntry) (targetLocal tag : Nat)
    (d : Nat := 0)
    (h : ∀ e ∈ borrows, e.targetLocal = targetLocal →
      e.tag = tag ∧ e.perm ≠ .reserved ∧ e.perm ≠ .reservedFrz true ∧ e.perm ≠ .reservedIM) :
    invalidateConflictingBorrows borrows targetLocal (some tag) d = borrows := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    rw [invalidateConflictingBorrows_cons,
      updateBorrowPerm_self_or_other e targetLocal tag d (h e (by simp)),
      ih (fun e' he' => h e' (by simp [he']))]

theorem updateBorrowPermAtProj_self_or_disjoint (e : BorrowEntry) (targetLocal tag : Nat)
    (writeProj : List ProjectionElem) (d : Nat := 0)
    (h : e.targetLocal = targetLocal →
      (e.tag = tag ∧ e.perm ≠ .reserved ∧ e.perm ≠ .reservedFrz true ∧ e.perm ≠ .reservedIM) ∨
      (e.tag ≠ tag ∧ MirSemantics.projectionsOverlap e.targetProjection writeProj = false)) :
    updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 d = e := by
  rcases e with ⟨etag, etloc, etproj, perm, eroff, erlen, eprot, eptag, etd, ead⟩
  unfold updateBorrowPermAtProj MirSemantics.treeBorrowWriterRelatedness
  cases htd : Nat.beq etd d with
  | false => rfl
  | true =>
    cases hloc : Nat.beq etloc targetLocal with
    | false => rfl
    | true =>
      dsimp only [Bool.and]
      rcases h (Nat.beq_eq.mp hloc) with ⟨heqTag, hnr1, hnr2, hnr3⟩ | ⟨hneTag, hdisj⟩
      · have htag : Nat.beq etag tag = true := Nat.beq_eq.mpr heqTag
        simp only [htag]
        cases perm with
        | reservedFrz c =>
          cases c
          · exact absurd rfl hnr1
          · exact absurd rfl hnr2
        | reservedIM => exact absurd rfl hnr3
        | cell | unique | frozen | disabled => rfl
      · have htag : Nat.beq etag tag = false := by
          cases hb : Nat.beq etag tag with
          | false => rfl
          | true => exact False.elim (hneTag (Nat.beq_eq.mp hb))
        have hov : borrowEntryOverlapsWrite ⟨etag, etloc, etproj, perm, eroff, erlen, eprot, eptag, etd, ead⟩ writeProj 0 0 = false := by
          simpa [borrowEntryOverlapsWrite] using hdisj
        simp [htag, hov]

theorem invalidateConflictingBorrowsAtProj_self_or_disjoint (borrows : List BorrowEntry)
    (targetLocal tag : Nat) (writeProj : List ProjectionElem) (d : Nat := 0)
    (h : ∀ e ∈ borrows, e.targetLocal = targetLocal →
      (e.tag = tag ∧ e.perm ≠ .reserved ∧ e.perm ≠ .reservedFrz true ∧ e.perm ≠ .reservedIM) ∨
      (e.tag ≠ tag ∧ MirSemantics.projectionsOverlap e.targetProjection writeProj = false)) :
    invalidateConflictingBorrowsAtProj borrows targetLocal (some tag) writeProj 0 0 d = borrows := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    simp only [invalidateConflictingBorrowsAtProj,
      updateBorrowPermAtProj_self_or_disjoint e targetLocal tag writeProj d (h e (by simp)),
      ih (fun e' he' => h e' (by simp [he']))]

/-- The Tree Borrows write transition of a write through tag `tag` keeps every
entry whose tag is an ancestor-or-self of `tag` (local write: `.reserved`
activates) or whose target is disjoint from the write (any writer). -/
theorem updateBorrowPermTreeAtProj_self_or_disjoint_keep (all : List BorrowEntry)
    (e : BorrowEntry) (targetLocal tag : Nat) (writeProj : List ProjectionElem) (d : Nat := 0)
    (h : e.targetLocal = targetLocal →
      MirSemantics.isBorrowDescendantOrSelf all tag e.tag = true ∨
      (e.tag ≠ tag ∧ MirSemantics.projectionsOverlap e.targetProjection writeProj = false)) :
    MirSemantics.updateBorrowPermTreeAtProj all e targetLocal (some tag) writeProj 0 0 d = e ∨
    MirSemantics.updateBorrowPermTreeAtProj all e targetLocal (some tag) writeProj 0 0 d =
      { e with perm := .active } := by
  unfold MirSemantics.updateBorrowPermTreeAtProj MirSemantics.resolveTreeBorrowWriterTag
  dsimp only
  cases hdesc : MirSemantics.isBorrowDescendantOrSelf all tag e.tag with
  | false =>
    exact updateBorrowPermAtProj_self_or_disjoint_keep e targetLocal tag writeProj d
      (fun hloc => .inr ((h hloc).resolve_left (by simp [hdesc])))
  | true =>
    exact updateBorrowPermAtProj_self_or_disjoint_keep e targetLocal e.tag writeProj d
      (fun _ => .inl rfl)

/-- General pointwise-map characterization of `invalidateDerefWriteBorrows` on a
write `(*_p) = _` through an unranged entry (`rangeOffset = 0`, `rangeLen = 0`)
whose resolved write projection is the entry's own projection
(`resolveDerefWriteFullProj = entry.targetProjection`, e.g. at offset `0` on a
`ptrTargetSpec` target, `resolveDerefWriteFullProj_of_ptrTargetSpec`): every entry
takes the Tree Borrows write transition `updateBorrowPermTreeAtProj`. -/
theorem invalidateDerefWriteBorrows_eq_map (locals : List LocalSlot) (borrows : List BorrowEntry)
    (p : Nat) (ptrVal : ProvenancePtr) (entry : BorrowEntry)
    (hp : locals[p]? = some (.init (.ptr ptrVal 8)))
    (he : lookupBorrow borrows ptrVal.tag = some entry)
    (hrlen : entry.rangeLen = 0) (hroff : entry.rangeOffset = 0)
    (hfull : MirSemantics.resolveDerefWriteFullProj locals locals (.ptr ptrVal 8) entry [] =
      entry.targetProjection) :
    invalidateDerefWriteBorrows locals borrows ⟨p, [.deref]⟩ [] =
      borrows.map (fun e =>
        MirSemantics.updateBorrowPermTreeAtProj borrows e entry.targetLocal (some ptrVal.tag)
          entry.targetProjection 0 0 entry.targetFrameDepth) := by
  rcases borrows with _ | ⟨b, _ | ⟨b2, rest⟩⟩
  · simp [lookupBorrow] at he
  · obtain ⟨hmem, htag⟩ := lookupBorrow_mem_and_tag he
    have hb : entry = b := by simpa using hmem
    subst hb
    have hres : MirSemantics.resolveTreeBorrowWriterTag [entry] entry (some ptrVal.tag) =
        some ptrVal.tag := by
      simp [MirSemantics.resolveTreeBorrowWriterTag, ← htag, isBorrowDescendantOrSelf_self]
    unfold invalidateDerefWriteBorrows
    simp only [get?, hp, he, hfull, List.map_cons,
      List.map_nil, MirSemantics.updateBorrowPermTreeAtProj, hres]
    cases htp : entry.targetProjection with
    | nil =>
      have hrl : Nat.beq entry.rangeLen 0 = true := by simp [hrlen]
      simp only [hrl, invalidateConflictingBorrows_eq_map, List.map_cons, List.map_nil]
    | cons ph pt =>
      rw [hroff, hrlen]
      simp only [invalidateConflictingBorrowsAtProj_eq_map, List.map_cons, List.map_nil]
  · unfold invalidateDerefWriteBorrows
    simp only [get?, hp, he, hfull, hroff, hrlen]
    exact invalidateTreeBorrowsAtProj_eq_map _ _ _ _ _ _ _ _

theorem invalidateDerefWriteBorrows_noop (locals : List LocalSlot) (borrows : List BorrowEntry)
    (p : Nat) (ptrVal : ProvenancePtr) (entry : BorrowEntry)
    (hp : locals[p]? = some (.init (.ptr ptrVal 8)))
    (he : lookupBorrow borrows ptrVal.tag = some entry)
    (hrlen : entry.rangeLen = 0) (hroff : entry.rangeOffset = 0)
    (hfull : MirSemantics.resolveDerefWriteFullProj locals locals (.ptr ptrVal 8) entry [] =
      entry.targetProjection)
    (hdisj : ∀ e ∈ borrows, e.targetLocal = entry.targetLocal →
      (e.tag = ptrVal.tag ∧ e.perm ≠ .reserved ∧ e.perm ≠ .reservedFrz true ∧ e.perm ≠ .reservedIM) ∨
      (MirSemantics.isBorrowDescendantOrSelf borrows ptrVal.tag e.tag = false ∧
        MirSemantics.projectionsOverlap e.targetProjection entry.targetProjection = false)) :
    invalidateDerefWriteBorrows locals borrows ⟨p, [.deref]⟩ [] = borrows := by
  rw [invalidateDerefWriteBorrows_eq_map locals borrows p ptrVal entry hp he hrlen hroff hfull]
  refine (List.map_congr_left ?_).trans (List.map_id borrows)
  intro e he_mem
  unfold MirSemantics.updateBorrowPermTreeAtProj MirSemantics.resolveTreeBorrowWriterTag
  by_cases hloc : e.targetLocal = entry.targetLocal
  · rcases hdisj e he_mem hloc with ⟨heqTag, hnr⟩ | ⟨hnd, hov⟩
    · have hd : MirSemantics.isBorrowDescendantOrSelf borrows ptrVal.tag e.tag = true := by
        rw [heqTag]; exact isBorrowDescendantOrSelf_self _ _
      simp only [hd]
      exact updateBorrowPermAtProj_self_or_disjoint e entry.targetLocal e.tag
        entry.targetProjection entry.targetFrameDepth (fun _ => .inl ⟨rfl, hnr⟩)
    · simp only [hnd]
      have hne : e.tag ≠ ptrVal.tag := by
        intro h
        rw [h, isBorrowDescendantOrSelf_self] at hnd
        cases hnd
      exact updateBorrowPermAtProj_self_or_disjoint e entry.targetLocal ptrVal.tag
        entry.targetProjection entry.targetFrameDepth (fun _ => .inr ⟨hne, hov⟩)
  · cases hd : MirSemantics.isBorrowDescendantOrSelf borrows ptrVal.tag e.tag
    · simp only [hd]
      exact updateBorrowPermAtProj_self_or_disjoint e entry.targetLocal ptrVal.tag
        entry.targetProjection entry.targetFrameDepth (fun hl => absurd hl hloc)
    · simp only [hd]
      exact updateBorrowPermAtProj_self_or_disjoint e entry.targetLocal e.tag
        entry.targetProjection entry.targetFrameDepth (fun hl => absurd hl hloc)

theorem writePlaceValue_deref_proj (locals : List LocalSlot) (borrows : List BorrowEntry)
    (p : Nat) (val : Value) (ptrVal : ProvenancePtr)
    (hp : locals[p]? = some (.init (.ptr ptrVal 8))) (entry : BorrowEntry)
    (he : lookupBorrow borrows ptrVal.tag = some entry)
    (hperm : entry.perm = .active ∨ entry.perm = .reserved)
    (ph : ProjectionElem) (pt : List ProjectionElem)
    (hproj : entry.targetProjection = ph :: pt)
    (rootVal rootVal' : Value) (ht : locals[entry.targetLocal]? = some (.init rootVal))
    (hw : writeProjectedValue locals rootVal (ph :: pt) val = .ok rootVal')
    (hthin : needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes = false) :
    writePlaceValue locals borrows ⟨p, [.deref]⟩ val =
      .ok (locals.set entry.targetLocal (.init rootVal')) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp ht
  have happ := appendProjections_nil_right pt
  rw [hproj] at hthin
  simp only [needsThinPtrElemResolution] at hthin
  rcases hperm with hperm | hperm <;>
    simp [writePlaceValue, get?, hp, he, hperm, hproj, happ, hget, hw, set?, hlt, hthin]

theorem evalOperand_deref_ub_of_not_init (locals : List LocalSlot) (p : Nat)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (layouts : Layout.LayoutTable) (callerLocals : List LocalSlot)
    (h : locals[p]? = some .uninit ∨ locals[p]? = some .dead) :
    evalOperand locals (.copy ⟨p, [.deref]⟩) borrows globals layouts callerLocals = .ub ∧
    evalOperand locals (.move ⟨p, [.deref]⟩) borrows globals layouts callerLocals = .ub := by
  rcases h with hu | hd
  · simp [evalOperand, get?, hu]
  · simp [evalOperand, get?, hd]

theorem evalOperand_move_deref_eq (locals : List LocalSlot) (p : Nat) (rest : List ProjectionElem)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (layouts : Layout.LayoutTable) (callerLocals : List LocalSlot) :
    evalOperand locals (.move ⟨p, .deref :: rest⟩) borrows globals layouts callerLocals =
      evalOperand locals (.copy ⟨p, .deref :: rest⟩) borrows globals layouts callerLocals :=
  rfl

/-! ## `ptrAliasingOk` consequences and `BorrowsOk` -/

theorem ptrDeclLayoutsOk_of_ptrAliasingOk {body : CapturedMir} (h : ptrAliasingOk body = true) :
    ptrDeclLayoutsOk body = true := by
  unfold ptrAliasingOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1

theorem ptrAliasingOk_spec {body : CapturedMir} (h : ptrAliasingOk body = true) :
    (∀ k ∈ bodyAddrTakenLocals body, 1 ≤ k ∧ k ≤ body.argCount) ∧
    (∀ bb ∈ body.basicBlocks,
      (∀ st ∈ bb.statements, stmtPreservesAddrTaken (bodyAddrTakenLocals body) st = true) ∧
      termPreservesAddrTaken (bodyAddrTakenLocals body) bb.terminator = true) ∧
    (subsumesPtrEnv body.localDecls.length (initPtrEnv body.localDecls.length)
        (ptrEnvAtEntry body 0) = true ∧
      ∀ blk < body.basicBlocks.length, ∀ bb, body.basicBlocks[blk]? = some bb →
        blockPtrAliasOk body.localDecls (ptrEnvAtEntry body blk) bb.statements = true ∧
        ∀ t ∈ termTargets bb.terminator,
          subsumesPtrEnv body.localDecls.length
            (bb.statements.foldl (ptrStmtStep body.localDecls) (ptrEnvAtEntry body blk))
            (ptrEnvAtEntry body t) = true) := by
  unfold ptrAliasingOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  rcases h with ⟨⟨⟨⟨_, h1⟩, h2⟩, h3⟩, h4⟩
  refine ⟨h1, h2, h3, fun blk hlt bb hbb => ?_⟩
  have hblk := h4 blk hlt
  rw [hbb] at hblk
  simp only [Bool.and_eq_true, List.all_eq_true] at hblk
  exact hblk

theorem directBorrowOf_rawPtr_of_nonDeref {mutbl : MirAst.Mutability} {q : Place}
    (hnd : ∀ rest, q.projection ≠ .deref :: rest) :
    directBorrowOf (.rawPtr mutbl q) = some (mutbl, q) := by
  rcases q with ⟨k, projs⟩
  cases projs with
  | nil => rfl
  | cons ph pt =>
    cases ph with
    | deref => exact False.elim (hnd pt rfl)
    | _ => rfl

theorem directBorrowOf_ref_of_nonDeref {bkind : BorrowKind} {q : Place}
    (hnd : ∀ rest, q.projection ≠ .deref :: rest) :
    directBorrowOf (.ref bkind q) = some (borrowKindMutbl bkind, q) := by
  rcases q with ⟨k, projs⟩
  cases projs with
  | nil => rfl
  | cons ph pt =>
    cases ph with
    | deref => exact False.elim (hnd pt rfl)
    | _ => rfl

theorem mem_bodyAddrTakenLocals_of_directBorrow {body : CapturedMir} {bb : BasicBlockData}
    {st : MirAst.Statement} {dst : Place} {rv : Rvalue} {mutbl : MirAst.Mutability} {q : Place}
    (hbb : bb ∈ body.basicBlocks) (hst : st ∈ bb.statements)
    (hkind : st.kind = .assign dst rv) (hdb : directBorrowOf rv = some (mutbl, q)) :
    q.local_ ∈ bodyAddrTakenLocals body := by
  unfold bodyAddrTakenLocals
  rw [List.mem_flatMap]
  refine ⟨bb, hbb, List.mem_filterMap.mpr ⟨st, hst, ?_⟩⟩
  simp [hkind, hdb]

theorem mem_bodyDirectBorrowPlaces_of_directBorrow {body : CapturedMir} {bb : BasicBlockData}
    {st : MirAst.Statement} {dst : Place} {rv : Rvalue} {mutbl : MirAst.Mutability} {q : Place}
    (hbb : bb ∈ body.basicBlocks) (hst : st ∈ bb.statements)
    (hkind : st.kind = .assign dst rv) (hdb : directBorrowOf rv = some (mutbl, q)) :
    q ∈ bodyDirectBorrowPlaces body := by
  unfold bodyDirectBorrowPlaces
  rw [List.mem_flatMap]
  refine ⟨bb, hbb, List.mem_filterMap.mpr ⟨st, hst, ?_⟩⟩
  simp [hkind, hdb]

theorem mem_bodyAddrTakenLocals {body : CapturedMir} {bb : BasicBlockData} {st : MirAst.Statement}
    {dst : Place} {mutbl : MirAst.Mutability} {q : Place}
    (hbb : bb ∈ body.basicBlocks) (hst : st ∈ bb.statements)
    (hkind : st.kind = .assign dst (.rawPtr mutbl q))
    (hnd : ∀ rest, q.projection ≠ .deref :: rest) :
    q.local_ ∈ bodyAddrTakenLocals body :=
  mem_bodyAddrTakenLocals_of_directBorrow hbb hst hkind (directBorrowOf_rawPtr_of_nonDeref hnd)

theorem stmtPreservesAddrTaken_not_target {addrLocals : List Nat} {st : MirAst.Statement}
    (h : stmtPreservesAddrTaken addrLocals st = true) :
    (∀ dst rv, st.kind = .assign dst rv → dst.local_ ∉ addrLocals) ∧
    (∀ p, st.kind = .deinit p → p.local_ ∉ addrLocals) ∧
    (∀ i, st.kind = .storageLive i → i ∉ addrLocals) ∧
    (∀ i, st.kind = .storageDead i → i ∉ addrLocals) := by
  obtain ⟨kind, span⟩ := st
  cases kind <;>
    simp_all [stmtPreservesAddrTaken, Bool.and_eq_true]

theorem foldl_moveOut_not_mem {ops : List Operand} {mo : List Nat} {k : Nat}
    (hk : k ∉ mo) (hops : ∀ op ∈ ops, opMoved op ≠ some k) :
    k ∉ ops.foldl moveOut mo := by
  induction ops generalizing mo with
  | nil => exact hk
  | cons op rest ih =>
    apply ih _ (fun op' h => hops op' (by simp [h]))
    unfold moveOut
    cases hm : opMoved op with
    | none => exact hk
    | some j =>
      have hjk : j ≠ k := fun h => hops op (by simp) (h ▸ hm)
      simp [hk, Ne.symm hjk]

theorem stmtMoved_not_addrTaken {addrLocals : List Nat} {st : MirAst.Statement} {mo : List Nat}
    {k : Nat} (hk_addr : k ∈ addrLocals) (hst : stmtPreservesAddrTaken addrLocals st = true)
    (hk_mo : k ∉ mo) :
    k ∉ stmtMoved mo st := by
  obtain ⟨kind, span⟩ := st
  cases kind with
  | assign dst rv =>
    simp only [stmtPreservesAddrTaken, Bool.and_eq_true, List.all_eq_true] at hst
    have hops : ∀ op ∈ rvOperands rv, opMoved op ≠ some k := by
      intro op hop heq
      have h2 := hst.2 op hop
      rw [heq] at h2
      simp [hk_addr] at h2
    have hn := foldl_moveOut_not_mem hk_mo hops
    rcases dst with ⟨i, projs⟩
    cases projs with
    | nil =>
      simp only [stmtMoved, List.mem_filter]
      exact fun h => hn h.1
    | cons _ _ =>
      simpa [stmtMoved] using hn
  | storageLive i | storageDead i =>
    simp only [stmtMoved, List.mem_filter]
    exact fun h => hk_mo h.1
  | deinit p =>
    rcases p with ⟨i, projs⟩
    cases projs <;> simp only [stmtMoved, List.mem_filter]
    · exact fun h => hk_mo h.1
    · exact hk_mo
  | intrinsic intr =>
    cases intr with
    | assume op =>
      simp only [stmtPreservesAddrTaken, List.all_cons, List.all_nil, Bool.and_true] at hst
      simp only [stmtMoved, moveOut]
      cases hm : opMoved op with
      | none => exact hk_mo
      | some j =>
        rw [hm] at hst
        have hjk : k ≠ j := fun h => by subst h; simp [hk_addr] at hst
        simp [hk_mo, hjk]
    | _ => simpa [stmtMoved] using hk_mo
  | _ => simpa [stmtMoved] using hk_mo

theorem termMoved_not_addrTaken {addrLocals : List Nat} {t : MirAst.Terminator} {mo : List Nat}
    {k : Nat} (hk_addr : k ∈ addrLocals) (ht : termPreservesAddrTaken addrLocals t = true)
    (hk_mo : k ∉ mo) :
    k ∉ termMoved mo t := by
  obtain ⟨kind, span⟩ := t
  cases kind with
  | switchInt discr _ =>
    simp only [termPreservesAddrTaken] at ht
    simp only [termMoved, moveOut]
    cases hm : opMoved discr with
    | none => exact hk_mo
    | some j =>
      rw [hm] at ht
      simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem] at ht
      have hjk : k ≠ j := fun h => ht (h ▸ hk_addr)
      simp [hk_mo, hjk]
  | call func args dst target unwind =>
    rcases dst with ⟨d, _ | ⟨_, _⟩⟩ <;> cases target <;>
      simp only [termMoved, List.mem_filter] <;>
      first | exact hk_mo | exact fun h => hk_mo h.1 | simpa using hk_mo
  | _ => simpa [termMoved] using hk_mo

theorem iterMovedEntries_not_addrTaken {body : CapturedMir} (hpa : ptrAliasingOk body = true)
    {k : Nat} (hk : k ∈ bodyAddrTakenLocals body) :
    ∀ (n : Nat) (blk : Nat), k ∉ (iterMovedEntries n body.basicBlocks []).getD blk [] := by
  obtain ⟨_, hpres, _⟩ := ptrAliasingOk_spec hpa
  have hfold_ss : ∀ (ss : List MirAst.Statement) (mo : List Nat),
      (∀ st ∈ ss, stmtPreservesAddrTaken (bodyAddrTakenLocals body) st = true) →
      k ∉ mo → k ∉ ss.foldl stmtMoved mo := by
    intro ss
    induction ss with
    | nil => intro mo _ hmo; exact hmo
    | cons s rest ih =>
      intro mo hss hmo
      exact ih (stmtMoved mo s) (fun st h => hss st (by simp [h]))
        (stmtMoved_not_addrTaken hk (hss s (by simp)) hmo)
  have hunion : ∀ (a b : List Nat), k ∉ a → k ∉ b → k ∉ unionLocals a b := by
    intro a b ha hb
    unfold unionLocals
    induction b generalizing a with
    | nil => exact ha
    | cons x xs ih =>
      simp only [List.foldl_cons]
      split
      · exact ih a ha (fun h => hb (by simp [h]))
      · have hkx : k ≠ x := fun h => hb (by simp [h])
        exact ih (x :: a) (by simp [ha, hkx]) (fun h => hb (by simp [h]))
  have hstep : ∀ (entries : List (List Nat)),
      (∀ b, k ∉ entries.getD b []) →
      ∀ b, k ∉ (stepMovedEntries body.basicBlocks entries).getD b [] := by
    intro entries hent b
    by_cases hb : b < body.basicBlocks.length
    · let stepFn : List Nat → Nat → List Nat := fun acc src =>
        match body.basicBlocks[src]? with
        | some bb =>
          if (termTargets bb.terminator).contains b then
            unionLocals acc (termMoved (bb.statements.foldl stmtMoved (entries.getD src [])) bb.terminator)
          else acc
        | none => acc
      have hget : (stepMovedEntries body.basicBlocks entries).getD b [] =
          (List.range body.basicBlocks.length).foldl stepFn (entries.getD b []) := by
        simp only [stepMovedEntries, stepFn, List.getD, List.getElem?_map,
          List.getElem?_range hb, Option.map_some, Option.getD_some]
        rfl
      rw [hget]
      suffices ∀ (srcs : List Nat) (acc : List Nat), k ∉ acc →
          k ∉ srcs.foldl stepFn acc from
        this _ _ (hent b)
      intro srcs
      induction srcs with
      | nil => intro acc hacc; exact hacc
      | cons src rest ih =>
        intro acc hacc
        apply ih
        dsimp only [stepFn]
        cases hsrc : body.basicBlocks[src]? with
        | none => exact hacc
        | some bb =>
          by_cases hc : (termTargets bb.terminator).contains b = true
          · simp only [hc, ↓reduceIte]
            obtain ⟨hss, htm⟩ := hpres bb (List.mem_of_getElem? hsrc)
            exact hunion acc _ hacc
              (termMoved_not_addrTaken hk htm (hfold_ss bb.statements _ hss (hent src)))
          · simp only [hc]
            exact hacc
    · have hlen : (stepMovedEntries body.basicBlocks entries).length = body.basicBlocks.length := by
        simp [stepMovedEntries]
      have hnone : (stepMovedEntries body.basicBlocks entries)[b]? = none :=
        List.getElem?_eq_none (by omega)
      simp [List.getD, hnone]
  suffices ∀ (n : Nat) (entries : List (List Nat)),
      (∀ b, k ∉ entries.getD b []) →
      ∀ b, k ∉ (iterMovedEntries n body.basicBlocks entries).getD b [] from
    fun n blk => this n [] (fun b => by simp [List.getD]) blk
  intro n
  induction n with
  | zero => intro entries hent b; exact hent b
  | succ m ih =>
    intro entries hent b
    simp only [iterMovedEntries]
    split
    · exact hent b
    · exact ih _ (hstep entries hent) b

theorem movedBefore_not_addrTaken {body : CapturedMir} (hpa : ptrAliasingOk body = true)
    (blk stmt : Nat) {k : Nat} (hk : k ∈ bodyAddrTakenLocals body) :
    k ∉ movedBefore body blk stmt := by
  have hent : k ∉ movedAtEntry body blk := iterMovedEntries_not_addrTaken hpa hk _ blk
  unfold movedBefore
  cases hbb : body.basicBlocks[blk]? with
  | none => exact hent
  | some bb =>
    obtain ⟨_, hpres, _⟩ := ptrAliasingOk_spec hpa
    obtain ⟨hss, _⟩ := hpres bb (List.mem_of_getElem? hbb)
    have htake : ∀ st ∈ bb.statements.take stmt,
        stmtPreservesAddrTaken (bodyAddrTakenLocals body) st = true :=
      fun st h => hss st (List.mem_of_mem_take h)
    have hstep : ∀ (ss' : List MirAst.Statement) (mo : List Nat),
        (∀ st ∈ ss', stmtPreservesAddrTaken (bodyAddrTakenLocals body) st = true) →
        k ∉ mo → k ∉ ss'.foldl stmtMoved mo := by
      intro ss'
      induction ss' with
      | nil => intro mo _ hmo; exact hmo
      | cons st0 tl ih' =>
        intro mo hs' hmo
        exact ih' _ (fun st1 h1 => hs' st1 (by simp [h1]))
          (stmtMoved_not_addrTaken hk (hs' st0 (by simp)) hmo)
    exact hstep (bb.statements.take stmt) (movedAtEntry body blk) htake hent

theorem StaleOk.addrTaken_eq {body : CapturedMir} {actual view : List LocalSlot} {blk stmt : Nat}
    (hstale : StaleOk body actual view blk stmt) (hpa : ptrAliasingOk body = true)
    {k : Nat} (hk : k ∈ bodyAddrTakenLocals body) :
    actual[k]? = view[k]? := by
  by_cases hne : actual[k]? = view[k]?
  · exact hne
  · exact False.elim (movedBefore_not_addrTaken hpa blk stmt hk (hstale.2 k hne).1)

private theorem trusted_length_eq {α : Type} : ∀ (xs : List α), length xs = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (trusted_length_eq xs)

theorem isBorrowDescendantOrSelfAux_mono {bs : List BorrowEntry} {c a : Nat} :
    ∀ {f1 f2 : Nat}, f1 ≤ f2 →
      MirSemantics.isBorrowDescendantOrSelfAux f1 bs c a = true →
      MirSemantics.isBorrowDescendantOrSelfAux f2 bs c a = true
  | 0, 0, _, h => h
  | 0, _ + 1, _, h => by
    unfold MirSemantics.isBorrowDescendantOrSelfAux at h ⊢
    rw [h]
  | k + 1, m + 1, hle, h => by
    unfold MirSemantics.isBorrowDescendantOrSelfAux at h ⊢
    cases hbeq : Nat.beq c a
    · rw [hbeq] at h
      dsimp only at h ⊢
      cases hlk : lookupBorrow bs c with
      | none => rw [hlk] at h; cases h
      | some e =>
        rw [hlk] at h
        dsimp only at h ⊢
        cases hp : e.parentTag with
        | none => rw [hp] at h; cases h
        | some pTag =>
          rw [hp] at h
          exact isBorrowDescendantOrSelfAux_mono (Nat.le_of_succ_le_succ hle) h
    · rfl

theorem isBorrowDescendantOrSelfAux_of_lookup_sub {bs bs' : List BorrowEntry}
    (hext : ∀ tag e, lookupBorrow bs tag = some e → lookupBorrow bs' tag = some e) :
    ∀ (fuel c a : Nat),
      MirSemantics.isBorrowDescendantOrSelfAux fuel bs c a = true →
      MirSemantics.isBorrowDescendantOrSelfAux fuel bs' c a = true
  | 0, _, _, h => h
  | fuel + 1, c, a, h => by
    unfold MirSemantics.isBorrowDescendantOrSelfAux at h ⊢
    cases hbeq : Nat.beq c a
    · rw [hbeq] at h
      dsimp only at h ⊢
      cases hlk : lookupBorrow bs c with
      | none => rw [hlk] at h; cases h
      | some e =>
        rw [hlk] at h
        rw [hext c e hlk]
        dsimp only at h ⊢
        cases hp : e.parentTag with
        | none => rw [hp] at h; cases h
        | some pTag =>
          rw [hp] at h
          exact isBorrowDescendantOrSelfAux_of_lookup_sub hext fuel pTag a h
    · rfl

theorem isBorrowDescendantOrSelf_of_lookup_sub {bs bs' : List BorrowEntry}
    (hext : ∀ tag e, lookupBorrow bs tag = some e → lookupBorrow bs' tag = some e)
    (hlen : bs.length ≤ bs'.length) {c a : Nat}
    (h : MirSemantics.isBorrowDescendantOrSelf bs c a = true) :
    MirSemantics.isBorrowDescendantOrSelf bs' c a = true := by
  unfold MirSemantics.isBorrowDescendantOrSelf at h ⊢
  rw [trusted_length_eq] at h ⊢
  exact isBorrowDescendantOrSelfAux_mono hlen
    (isBorrowDescendantOrSelfAux_of_lookup_sub hext bs.length c a h)

theorem isBorrowDescendantOrSelfAux_map_eq {bs : List BorrowEntry} {f : BorrowEntry → BorrowEntry}
    (hf_tag : ∀ e, (f e).tag = e.tag) (hf_parent : ∀ e, (f e).parentTag = e.parentTag) :
    ∀ (fuel c a : Nat),
      MirSemantics.isBorrowDescendantOrSelfAux fuel (bs.map f) c a =
        MirSemantics.isBorrowDescendantOrSelfAux fuel bs c a
  | 0, _, _ => rfl
  | fuel + 1, c, a => by
    unfold MirSemantics.isBorrowDescendantOrSelfAux
    cases Nat.beq c a with
    | true => rfl
    | false =>
      rw [lookupBorrow_map_eq hf_tag c]
      cases lookupBorrow bs c with
      | none => rfl
      | some e =>
        dsimp only [Option.map]
        rw [hf_parent e]
        cases e.parentTag with
        | none => rfl
        | some pTag => exact isBorrowDescendantOrSelfAux_map_eq hf_tag hf_parent fuel pTag a

theorem isBorrowDescendantOrSelf_map_eq {bs : List BorrowEntry} {f : BorrowEntry → BorrowEntry}
    (hf_tag : ∀ e, (f e).tag = e.tag) (hf_parent : ∀ e, (f e).parentTag = e.parentTag)
    (c a : Nat) :
    MirSemantics.isBorrowDescendantOrSelf (bs.map f) c a =
      MirSemantics.isBorrowDescendantOrSelf bs c a := by
  unfold MirSemantics.isBorrowDescendantOrSelf
  rw [trusted_length_eq, trusted_length_eq, List.length_map]
  exact isBorrowDescendantOrSelfAux_map_eq hf_tag hf_parent bs.length c a

theorem isBorrowDescendantOrSelf_cons_child {entry : BorrowEntry} {bs : List BorrowEntry}
    {pTag a : Nat} (hp : entry.parentTag = some pTag)
    (hext : ∀ tag e, lookupBorrow bs tag = some e → lookupBorrow (entry :: bs) tag = some e)
    (h : MirSemantics.isBorrowDescendantOrSelf bs pTag a = true) :
    MirSemantics.isBorrowDescendantOrSelf (entry :: bs) entry.tag a = true := by
  unfold MirSemantics.isBorrowDescendantOrSelf at h ⊢
  rw [trusted_length_eq] at h ⊢
  simp only [List.length_cons]
  unfold MirSemantics.isBorrowDescendantOrSelfAux
  cases Nat.beq entry.tag a with
  | true => rfl
  | false =>
    have hself : lookupBorrow (entry :: bs) entry.tag = some entry := by
      simp [lookupBorrow]
    rw [hself]
    dsimp only
    rw [hp]
    exact isBorrowDescendantOrSelfAux_of_lookup_sub hext bs.length pTag a h

/-- `a` is reachable from `c` along `BorrowEntry.parentTag` links in `borrows`
for some finite fuel. -/
def IsBorrowAncestorOrSelf (borrows : List BorrowEntry) (c a : Nat) : Prop :=
  ∃ fuel, MirSemantics.isBorrowDescendantOrSelfAux fuel borrows c a = true

theorem IsBorrowAncestorOrSelf.refl (borrows : List BorrowEntry) (t : Nat) :
    IsBorrowAncestorOrSelf borrows t t :=
  ⟨1, isBorrowDescendantOrSelfAux_self 1 borrows t⟩

theorem IsBorrowAncestorOrSelf.of_eq {borrows : List BorrowEntry} {c a : Nat} (h : c = a) :
    IsBorrowAncestorOrSelf borrows c a :=
  h ▸ IsBorrowAncestorOrSelf.refl borrows c

theorem IsBorrowAncestorOrSelf.of_descendant {borrows : List BorrowEntry} {c a : Nat}
    (h : MirSemantics.isBorrowDescendantOrSelf borrows c a = true) :
    IsBorrowAncestorOrSelf borrows c a :=
  ⟨length borrows, h⟩

theorem IsBorrowAncestorOrSelf.step {borrows : List BorrowEntry} {c pTag a : Nat}
    {entry : BorrowEntry} (hlk : lookupBorrow borrows c = some entry)
    (hp : entry.parentTag = some pTag)
    (h : IsBorrowAncestorOrSelf borrows pTag a) :
    IsBorrowAncestorOrSelf borrows c a := by
  obtain ⟨fuel, hf⟩ := h
  refine ⟨fuel + 1, ?_⟩
  unfold MirSemantics.isBorrowDescendantOrSelfAux
  cases Nat.beq c a with
  | true => rfl
  | false =>
    rw [hlk]
    dsimp only
    rw [hp]
    exact hf

theorem isBorrowDescendantOrSelfAux_trans {borrows : List BorrowEntry} :
    ∀ {f1 c b a : Nat},
      MirSemantics.isBorrowDescendantOrSelfAux f1 borrows c b = true →
      IsBorrowAncestorOrSelf borrows b a →
      IsBorrowAncestorOrSelf borrows c a
  | 0, _, _, _, h1, h2 => by
    unfold MirSemantics.isBorrowDescendantOrSelfAux at h1
    rw [Nat.beq_eq.mp h1]
    exact h2
  | f1 + 1, c, b, a, h1, h2 => by
    unfold MirSemantics.isBorrowDescendantOrSelfAux at h1
    cases hcb : Nat.beq c b with
    | true =>
      have heq : c = b := Nat.beq_eq.mp hcb
      subst heq
      exact h2
    | false =>
      rw [hcb] at h1
      dsimp only at h1
      cases hlk : lookupBorrow borrows c with
      | none => rw [hlk] at h1; cases h1
      | some e =>
        rw [hlk] at h1
        dsimp only at h1
        cases hp : e.parentTag with
        | none => rw [hp] at h1; cases h1
        | some pTag =>
          rw [hp] at h1
          exact IsBorrowAncestorOrSelf.step hlk hp (isBorrowDescendantOrSelfAux_trans h1 h2)

theorem IsBorrowAncestorOrSelf.trans {borrows : List BorrowEntry} {c b a : Nat}
    (h1 : IsBorrowAncestorOrSelf borrows c b) (h2 : IsBorrowAncestorOrSelf borrows b a) :
    IsBorrowAncestorOrSelf borrows c a := by
  obtain ⟨f1, hf1⟩ := h1
  exact isBorrowDescendantOrSelfAux_trans hf1 h2

theorem IsBorrowAncestorOrSelf.of_lookup_sub {bs bs' : List BorrowEntry}
    (hext : ∀ tag e, lookupBorrow bs tag = some e → lookupBorrow bs' tag = some e)
    {c a : Nat} (h : IsBorrowAncestorOrSelf bs c a) :
    IsBorrowAncestorOrSelf bs' c a := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, isBorrowDescendantOrSelfAux_of_lookup_sub hext fuel c a hf⟩

theorem IsBorrowAncestorOrSelf.map_iff {bs : List BorrowEntry} {f : BorrowEntry → BorrowEntry}
    (hf_tag : ∀ e, (f e).tag = e.tag) (hf_parent : ∀ e, (f e).parentTag = e.parentTag)
    {c a : Nat} :
    IsBorrowAncestorOrSelf (bs.map f) c a ↔ IsBorrowAncestorOrSelf bs c a := by
  constructor <;> (rintro ⟨fuel, hf⟩; refine ⟨fuel, ?_⟩)
  · rwa [isBorrowDescendantOrSelfAux_map_eq hf_tag hf_parent] at hf
  · rwa [isBorrowDescendantOrSelfAux_map_eq hf_tag hf_parent]

theorem IsBorrowAncestorOrSelf.cases_of_lookup {bs : List BorrowEntry} {c a : Nat}
    {entry : BorrowEntry} (hlk : lookupBorrow bs c = some entry)
    (h : IsBorrowAncestorOrSelf bs c a) :
    c = a ∨ ∃ pTag, entry.parentTag = some pTag ∧ IsBorrowAncestorOrSelf bs pTag a := by
  obtain ⟨fuel, hf⟩ := h
  cases fuel with
  | zero =>
    unfold MirSemantics.isBorrowDescendantOrSelfAux at hf
    exact .inl (Nat.beq_eq.mp hf)
  | succ f =>
    unfold MirSemantics.isBorrowDescendantOrSelfAux at hf
    cases hbeq : Nat.beq c a with
    | true => exact .inl (Nat.beq_eq.mp hbeq)
    | false =>
      rw [hbeq, hlk] at hf
      dsimp only at hf
      cases hp : entry.parentTag with
      | none => rw [hp] at hf; cases hf
      | some pTag =>
        rw [hp] at hf
        exact .inr ⟨pTag, rfl, f, hf⟩

private theorem lookupBorrow_cons_of_ne (e : BorrowEntry) (rest : List BorrowEntry) (tag : Nat)
    (h : e.tag ≠ tag) : lookupBorrow (e :: rest) tag = lookupBorrow rest tag := by
  have hb : Nat.beq e.tag tag = false := by
    cases hb : Nat.beq e.tag tag with
    | false => rfl
    | true => exact absurd (Nat.beq_eq.mp hb) h
  simp only [lookupBorrow, hb]

/-- Reverse-chronological borrow-tree ordering: every entry `e` prepended before
`rest` has `b.tag < e.tag` for all `b ∈ rest`, and any `e.parentTag = some pt`
resolves via `lookupBorrow rest pt`. -/
def BorrowDagOrdered : List BorrowEntry → Prop
  | [] => True
  | e :: rest =>
    (∀ pt, e.parentTag = some pt → ∃ b, lookupBorrow rest pt = some b) ∧
    (∀ b ∈ rest, b.tag < e.tag) ∧
    BorrowDagOrdered rest

theorem BorrowDagOrdered.map {bs : List BorrowEntry} {f : BorrowEntry → BorrowEntry}
    (hf_tag : ∀ e, (f e).tag = e.tag) (hf_parent : ∀ e, (f e).parentTag = e.parentTag)
    (hdag : BorrowDagOrdered bs) : BorrowDagOrdered (bs.map f) := by
  induction bs with
  | nil => trivial
  | cons e rest ih =>
    obtain ⟨hpt, hlt, hrest⟩ := hdag
    refine ⟨fun pt hp => ?_, fun b hb => ?_, ih hrest⟩
    · rw [hf_parent e] at hp
      obtain ⟨b, hlk⟩ := hpt pt hp
      exact ⟨f b, by rw [lookupBorrow_map_eq hf_tag, hlk]; rfl⟩
    · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
      rw [hf_tag b0, hf_tag e]
      exact hlt b0 hb0

theorem BorrowDagOrdered.parent_lt_of_lookup {bs : List BorrowEntry}
    (hdag : BorrowDagOrdered bs) :
    ∀ {c pt : Nat} {b : BorrowEntry},
      lookupBorrow bs c = some b → b.parentTag = some pt →
      ∃ p, lookupBorrow bs pt = some p ∧ pt < b.tag := by
  induction bs with
  | nil => intro _ _ _ hlk _; simp [lookupBorrow] at hlk
  | cons e rest ih =>
    intro c pt b hlk hp
    obtain ⟨hpt, hlt, hrest⟩ := hdag
    unfold lookupBorrow at hlk
    cases hb : Nat.beq e.tag c with
    | true =>
      rw [hb] at hlk
      injection hlk with heq
      subst heq
      obtain ⟨p, hlk_p⟩ := hpt pt hp
      obtain ⟨hp_mem, hp_tag⟩ := lookupBorrow_mem_and_tag hlk_p
      have hpt_lt : pt < e.tag := hp_tag ▸ hlt p hp_mem
      have hne : e.tag ≠ pt := by omega
      exact ⟨p, by rw [lookupBorrow_cons_of_ne e rest pt hne]; exact hlk_p, hpt_lt⟩
    | false =>
      rw [hb] at hlk
      obtain ⟨p, hlk_p, hpt_lt⟩ := ih hrest hlk hp
      obtain ⟨hb_mem, _⟩ := lookupBorrow_mem_and_tag hlk
      have hb_lt : b.tag < e.tag := hlt b hb_mem
      have hne : e.tag ≠ pt := by omega
      exact ⟨p, by rw [lookupBorrow_cons_of_ne e rest pt hne]; exact hlk_p, hpt_lt⟩

theorem isBorrowDescendantOrSelfAux_cons_of_lt {e : BorrowEntry} {rest : List BorrowEntry}
    (hdag : BorrowDagOrdered (e :: rest)) :
    ∀ (fuel : Nat) {c : Nat} (a : Nat),
      c < e.tag →
      MirSemantics.isBorrowDescendantOrSelfAux fuel (e :: rest) c a =
        MirSemantics.isBorrowDescendantOrSelfAux fuel rest c a
  | 0, _, _, _ => rfl
  | fuel + 1, c, a, hlt_c => by
    unfold MirSemantics.isBorrowDescendantOrSelfAux
    cases Nat.beq c a with
    | true => rfl
    | false =>
      have hne : e.tag ≠ c := by omega
      rw [lookupBorrow_cons_of_ne e rest c hne]
      cases hlk : lookupBorrow rest c with
      | none => rfl
      | some b =>
        dsimp only
        cases hp : b.parentTag with
        | none => rfl
        | some pt =>
          obtain ⟨_, _, hpt_lt⟩ := hdag.2.2.parent_lt_of_lookup hlk hp
          have hlt_b : b.tag < e.tag := hdag.2.1 b (lookupBorrow_mem_and_tag hlk).1
          exact isBorrowDescendantOrSelfAux_cons_of_lt hdag fuel a (by omega)

theorem IsBorrowAncestorOrSelf.cons_of_lt_iff {e : BorrowEntry} {rest : List BorrowEntry}
    (hdag : BorrowDagOrdered (e :: rest)) {c a : Nat} (hlt_c : c < e.tag) :
    IsBorrowAncestorOrSelf (e :: rest) c a ↔ IsBorrowAncestorOrSelf rest c a := by
  constructor <;> (rintro ⟨fuel, hf⟩; refine ⟨fuel, ?_⟩)
  · rwa [isBorrowDescendantOrSelfAux_cons_of_lt hdag fuel a hlt_c] at hf
  · rwa [isBorrowDescendantOrSelfAux_cons_of_lt hdag fuel a hlt_c]

theorem BorrowDagOrdered.descendant_of_ancestor {bs : List BorrowEntry}
    (hdag : BorrowDagOrdered bs) :
    ∀ {c a : Nat} {ec : BorrowEntry},
      lookupBorrow bs c = some ec →
      IsBorrowAncestorOrSelf bs c a →
      MirSemantics.isBorrowDescendantOrSelf bs c a = true := by
  induction bs with
  | nil => intro _ _ _ hlk _; simp [lookupBorrow] at hlk
  | cons e rest ih =>
    intro c a ec hlk ⟨fuel, hf⟩
    unfold MirSemantics.isBorrowDescendantOrSelf
    rw [trusted_length_eq]
    simp only [List.length_cons]
    cases fuel with
    | zero =>
      unfold MirSemantics.isBorrowDescendantOrSelfAux at hf ⊢
      rw [hf]
    | succ f =>
      unfold MirSemantics.isBorrowDescendantOrSelfAux at hf ⊢
      cases hca : Nat.beq c a with
      | true => rfl
      | false =>
        rw [hca] at hf
        dsimp only at hf ⊢
        have hlk' := hlk
        unfold lookupBorrow at hlk'
        cases hec : Nat.beq e.tag c with
        | true =>
          rw [hec] at hlk'
          injection hlk' with heq
          subst heq
          have htag_eq : e.tag = c := Nat.beq_eq.mp hec
          rw [hlk] at hf ⊢
          dsimp only at hf ⊢
          cases hp : e.parentTag with
          | none => rw [hp] at hf; cases hf
          | some pt =>
            rw [hp] at hf
            dsimp only at hf ⊢
            obtain ⟨b, hlk_pt⟩ := hdag.1 pt hp
            have hpt_lt : pt < e.tag :=
              (lookupBorrow_mem_and_tag hlk_pt).2 ▸ hdag.2.1 b (lookupBorrow_mem_and_tag hlk_pt).1
            rw [isBorrowDescendantOrSelfAux_cons_of_lt hdag f a hpt_lt] at hf
            have hih := ih hdag.2.2 hlk_pt ⟨f, hf⟩
            unfold MirSemantics.isBorrowDescendantOrSelf at hih
            rw [trusted_length_eq] at hih
            rw [isBorrowDescendantOrSelfAux_cons_of_lt hdag rest.length a hpt_lt]
            exact hih
        | false =>
          rw [hec] at hlk'
          have hc_lt : c < e.tag :=
            (lookupBorrow_mem_and_tag hlk').2 ▸ hdag.2.1 ec (lookupBorrow_mem_and_tag hlk').1
          have hf_full : MirSemantics.isBorrowDescendantOrSelfAux (f + 1) (e :: rest) c a = true := by
            unfold MirSemantics.isBorrowDescendantOrSelfAux
            rw [hca]
            exact hf
          rw [isBorrowDescendantOrSelfAux_cons_of_lt hdag (f + 1) a hc_lt] at hf_full
          have hih := ih hdag.2.2 hlk' ⟨f + 1, hf_full⟩
          unfold MirSemantics.isBorrowDescendantOrSelf at hih
          rw [trusted_length_eq] at hih
          have hih' : MirSemantics.isBorrowDescendantOrSelfAux (rest.length + 1) (e :: rest) c a = true := by
            rw [isBorrowDescendantOrSelfAux_cons_of_lt hdag (rest.length + 1) a hc_lt]
            exact isBorrowDescendantOrSelfAux_mono (Nat.le_succ _) hih
          unfold MirSemantics.isBorrowDescendantOrSelfAux at hih'
          rw [hca] at hih'
          exact hih'

theorem treeBorrowChainChildAccessUBAux_write_false {borrows : List BorrowEntry} :
    ∀ (fuel : Nat) (pOpt : Option Nat),
      (∀ tag, pOpt = some tag →
        ∀ anc ∈ borrows, IsBorrowAncestorOrSelf borrows tag anc.tag →
          anc.perm ≠ .disabled ∧ anc.perm ≠ .frozen) →
      MirSemantics.treeBorrowChainChildAccessUBAux .write fuel borrows pOpt = false
  | 0, _, _ => rfl
  | fuel + 1, none, _ => rfl
  | fuel + 1, some tag, hok => by
    unfold MirSemantics.treeBorrowChainChildAccessUBAux
    cases hlk : lookupBorrow borrows tag with
    | none => rfl
    | some anc =>
      dsimp only
      obtain ⟨hmem, htag⟩ := lookupBorrow_mem_and_tag hlk
      obtain ⟨hndis, hnf⟩ := hok tag rfl anc hmem (IsBorrowAncestorOrSelf.of_eq htag.symm)
      have hub : MirSemantics.treeBorrowTransitionIsUB
          (MirSemantics.treeBorrowPermTransition .write .localAccess anc.perm false) = false := by
        cases hpe : anc.perm with
        | disabled => exact absurd hpe hndis
        | frozen => exact absurd hpe hnf
        | cell | reservedIM | unique => rfl
        | reservedFrz c => cases c <;> rfl
      rw [hub]
      exact treeBorrowChainChildAccessUBAux_write_false fuel anc.parentTag
        (fun pTag hp a ha hanc =>
          hok tag rfl a ha (IsBorrowAncestorOrSelf.step hlk hp hanc))

theorem derefWriteTreeUB_false_of_ancestors_writable (locals : List LocalSlot)
    (borrows : List BorrowEntry) (w : Nat)
    (hw : ∀ ptrVal sz, locals[w]? = some (.init (.ptr ptrVal sz)) →
      ∀ anc ∈ borrows, IsBorrowAncestorOrSelf borrows ptrVal.tag anc.tag →
        anc.perm ≠ .disabled ∧ anc.perm ≠ .frozen) :
    MirSemantics.derefWriteTreeUB locals borrows ⟨w, [.deref]⟩ = false := by
  unfold MirSemantics.derefWriteTreeUB
  rcases borrows with _ | ⟨b1, _ | ⟨b2, bs⟩⟩
  · rfl
  · rfl
  · simp only [get?]
    cases hloc : locals[w]? with
    | none => rfl
    | some slot =>
      cases slot with
      | uninit | dead => rfl
      | init val =>
        cases val with
        | ptr ptrVal sz =>
          dsimp only
          cases hlk : lookupBorrow (b1 :: b2 :: bs) ptrVal.tag with
          | none => rfl
          | some entry =>
            exact treeBorrowChainChildAccessUBAux_write_false _ entry.parentTag
              (fun pTag hp anc hmem hanc =>
                hw ptrVal sz hloc anc hmem (IsBorrowAncestorOrSelf.step hlk hp hanc))
        | unit | uninit | scalar _ | aggregate _ _ => rfl

/-- Concrete meaning of `PtrLocalState` for local `p` at runtime slots `view`
and Anneal borrow table `borrows`:
* `.empty` (`⊥`): `p` holds no initialized 8-byte pointer;
* `.live target peers hot writable`: if `p` holds an initialized pointer `pv`,
  its borrow entry and every ancestor `anc` in `borrows` (`IsBorrowAncestorOrSelf`)
  are not `.disabled`, are not `.frozen` when `writable = true` and `p` is a
  mutable pointer/reference local (`isMutPtrLocal`), are not `.active` when
  `hot = false` and `p` is a mutable local, share the same static target place,
  match `target` (when `some`), and `pv.tag` is in the Tree Borrows subtree of
  every initialized pointer/reference local in `peers`
  (`isBorrowDescendantOrSelf borrows pv.tag pv_r.tag = true`);
* `.disabled` (`⊤`): unconstrained (`True`). -/
def PtrLocalOk (body : CapturedMir) (view : List LocalSlot) (borrows : List BorrowEntry)
    (p : Nat) : PtrLocalState → Prop
  | .empty =>
    ∀ dp pv, body.localDecls[p]? = some dp → isPtrTy dp.ty = true →
      view[p]? ≠ some (.init (.ptr pv 8))
  | .live target peers hot writable =>
    ∀ dp pv, body.localDecls[p]? = some dp → isPtrTy dp.ty = true →
      view[p]? = some (.init (.ptr pv 8)) →
      (∃ entry, lookupBorrow borrows pv.tag = some entry ∧ entry.perm ≠ .disabled ∧
        (writable = true → isMutPtrLocal body.localDecls p = true → entry.perm ≠ .frozen) ∧
        (isMutPtrLocal body.localDecls p = true → hot = false → entry.perm ≠ .active) ∧
        (∀ q, target = some q → (entry.targetLocal, borrowProjSteps entry.targetProjection) = q) ∧
        (∀ anc ∈ borrows, IsBorrowAncestorOrSelf borrows pv.tag anc.tag →
          anc.perm ≠ .disabled ∧
          (writable = true → isMutPtrLocal body.localDecls p = true → anc.perm ≠ .frozen) ∧
          (isMutPtrLocal body.localDecls p = true → hot = false → anc.perm ≠ .active) ∧
          (anc.targetLocal, borrowProjSteps anc.targetProjection) =
            (entry.targetLocal, borrowProjSteps entry.targetProjection))) ∧
      (∀ r ∈ peers, ∀ dr pv_r, body.localDecls[r]? = some dr → isPtrTy dr.ty = true →
        view[r]? = some (.init (.ptr pv_r 8)) →
        MirSemantics.isBorrowDescendantOrSelf borrows pv.tag pv_r.tag = true)
  | .disabled => True

/-- Pointwise `PtrLocalOk` across all declared locals `0 .. body.localDecls.length - 1`. -/
def PtrEnvOk (body : CapturedMir) (view : List LocalSlot) (borrows : List BorrowEntry)
    (env : List PtrLocalState) : Prop :=
  ∀ p < body.localDecls.length, PtrLocalOk body view borrows p (env.getD p .disabled)

theorem PtrLocalOk.of_empty {body : CapturedMir} {view : List LocalSlot}
    {borrows : List BorrowEntry} {p : Nat}
    (h : PtrLocalOk body view borrows p .empty) (s : PtrLocalState) :
    PtrLocalOk body view borrows p s := by
  cases s with
  | empty => exact h
  | live _ _ _ _ =>
    intro dp pv hdp hpty hv
    exact False.elim (h dp pv hdp hpty hv)
  | disabled => trivial

theorem PtrLocalOk.of_subsumes {body : CapturedMir} {view : List LocalSlot}
    {borrows : List BorrowEntry} {p : Nat} {s1 s2 : PtrLocalState}
    (hsub : subsumesPtrLocalState s1 s2 = true)
    (hok : PtrLocalOk body view borrows p s1) :
    PtrLocalOk body view borrows p s2 := by
  cases s1 with
  | empty => exact hok.of_empty s2
  | disabled =>
    cases s2 <;> first | trivial | (simp [subsumesPtrLocalState] at hsub)
  | live t1 ps1 h1 w1 =>
    cases s2 with
    | empty => simp [subsumesPtrLocalState] at hsub
    | disabled => trivial
    | live t2 ps2 h2 w2 =>
      simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
        List.contains_iff_mem] at hsub
      obtain ⟨⟨⟨hh, hw⟩, ht⟩, hps⟩ := hsub
      intro dp pv hdp hpty hv
      obtain ⟨⟨entry, hlk, hndis, hnf1, hnact1, ht1, hanc1⟩, hpeers1⟩ := hok dp pv hdp hpty hv
      have hw1 : w2 = true → w1 = true := fun hw2 => by subst hw2; cases w1 <;> simp_all
      have hh1 : h2 = false → h1 = false := fun hh2 => by subst hh2; cases h1 <;> simp_all
      refine ⟨⟨entry, hlk, hndis,
        fun hw2 hm => hnf1 (hw1 hw2) hm,
        fun hm hh2 => hnact1 hm (hh1 hh2),
        fun q hq => ?_,
        fun anc hmem hanc => ?_⟩,
        fun r hr dr pv_r hdr hptr hvr =>
          hpeers1 r (hps r hr) dr pv_r hdr hptr hvr⟩
      · rw [hq] at ht
        simp only [decide_eq_true_eq] at ht
        exact ht1 q ht
      · obtain ⟨ha_ndis, ha_nf, ha_nact, ha_tgt⟩ := hanc1 anc hmem hanc
        exact ⟨ha_ndis, fun hw2 hm => ha_nf (hw1 hw2) hm,
          fun hm hh2 => ha_nact hm (hh1 hh2), ha_tgt⟩

theorem PtrEnvOk.of_subsumes {body : CapturedMir} {view : List LocalSlot}
    {borrows : List BorrowEntry} {e1 e2 : List PtrLocalState}
    (hsub : subsumesPtrEnv body.localDecls.length e1 e2 = true)
    (hok : PtrEnvOk body view borrows e1) :
    PtrEnvOk body view borrows e2 := by
  simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range] at hsub
  intro p hp
  exact (hok p hp).of_subsumes (hsub p hp)

theorem getD_map_range {α : Type} (n : Nat) (f : Nat → α) (d : α) {p : Nat} (hp : p < n) :
    ((List.range n).map f).getD p d = f p := by
  simp [List.getD, List.getElem?_map, List.getElem?_range hp]

theorem PtrEnvOk.of_map_range {body : CapturedMir} {view : List LocalSlot}
    {borrows : List BorrowEntry} {env : List PtrLocalState}
    (hok : PtrEnvOk body view borrows env) :
    PtrEnvOk body view borrows
      ((List.range body.localDecls.length).map (fun q => env.getD q .disabled)) := by
  intro p hp
  rw [getD_map_range _ _ _ hp]
  exact hok p hp

private theorem foldl_take_succ {α β : Type} (f : α → β → α) (xs : List β) (acc : α)
    {idx : Nat} {x : β} (hx : xs[idx]? = some x) :
    (xs.take (idx + 1)).foldl f acc = f ((xs.take idx).foldl f acc) x := by
  induction xs generalizing idx acc with
  | nil => simp at hx
  | cons y ys ih =>
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      rfl
    | succ idx' =>
      rw [List.getElem?_cons_succ] at hx
      simp only [List.take_succ_cons, List.foldl_cons]
      exact ih (f acc y) hx

theorem ptrEnvBefore_zero (body : CapturedMir) (blk : Nat) :
    ptrEnvBefore body blk 0 = ptrEnvAtEntry body blk := by
  unfold ptrEnvBefore
  cases body.basicBlocks[blk]? <;> rfl

theorem ptrEnvBefore_succ {body : CapturedMir} {blk idx : Nat} {bb : BasicBlockData}
    {st : MirAst.Statement} (hbb : body.basicBlocks[blk]? = some bb)
    (hst : bb.statements[idx]? = some st) :
    ptrEnvBefore body blk (idx + 1) =
      ptrStmtStep body.localDecls (ptrEnvBefore body blk idx) st := by
  unfold ptrEnvBefore
  rw [hbb]
  exact foldl_take_succ (ptrStmtStep body.localDecls) bb.statements (ptrEnvAtEntry body blk) hst

theorem ptrEnvBefore_of_length_le {body : CapturedMir} {blk idx : Nat} {bb : BasicBlockData}
    (hbb : body.basicBlocks[blk]? = some bb) (hle : bb.statements.length ≤ idx) :
    ptrEnvBefore body blk idx =
      bb.statements.foldl (ptrStmtStep body.localDecls) (ptrEnvAtEntry body blk) := by
  unfold ptrEnvBefore
  rw [hbb]
  dsimp only []
  rw [List.take_of_length_le hle]

theorem blockPtrAliasOk_getElem? {decls : List LocalDecl} {ss : List MirAst.Statement}
    {env : List PtrLocalState} (hok : blockPtrAliasOk decls env ss = true)
    {idx : Nat} {st : MirAst.Statement} (hst : ss[idx]? = some st) :
    ptrStmtOk ((ss.take idx).foldl (ptrStmtStep decls) env) st = true := by
  induction ss generalizing idx env with
  | nil => simp at hst
  | cons s rest ih =>
    simp only [blockPtrAliasOk, Bool.and_eq_true] at hok
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hst
      subst hst
      exact hok.1
    | succ idx' =>
      rw [List.getElem?_cons_succ] at hst
      simp only [List.take_succ_cons, List.foldl_cons]
      exact ih hok.2 hst

/-- Every statement reachable in a `ptrAliasingOk` body satisfies `ptrStmtOk` at
its static `ptrEnvBefore`. -/
theorem ptrStmtOk_of_ptrAliasingOk {body : CapturedMir} (hpa : ptrAliasingOk body = true)
    {blk idx : Nat} {bb : BasicBlockData} {st : MirAst.Statement}
    (hbb : body.basicBlocks[blk]? = some bb) (hst : bb.statements[idx]? = some st) :
    ptrStmtOk (ptrEnvBefore body blk idx) st = true := by
  have hblk_lt : blk < body.basicBlocks.length := (List.getElem?_eq_some_iff.mp hbb).1
  obtain ⟨_, _, _, hblks⟩ := ptrAliasingOk_spec hpa
  obtain ⟨hbok, _⟩ := hblks blk hblk_lt bb hbb
  unfold ptrEnvBefore
  rw [hbb]
  exact blockPtrAliasOk_getElem? hbok hst

theorem ptrEnvBefore_jump_subsumes {body : CapturedMir} (hpa : ptrAliasingOk body = true)
    {blk idx : Nat} {bb : BasicBlockData} (hbb : body.basicBlocks[blk]? = some bb)
    (hle : bb.statements.length ≤ idx) {target : Nat}
    (htgt : target ∈ termTargets bb.terminator) :
    subsumesPtrEnv body.localDecls.length
      (ptrEnvBefore body blk idx) (ptrEnvBefore body target 0) = true := by
  have hblk_lt : blk < body.basicBlocks.length := (List.getElem?_eq_some_iff.mp hbb).1
  obtain ⟨_, _, _, hblks⟩ := ptrAliasingOk_spec hpa
  obtain ⟨_, hedges⟩ := hblks blk hblk_lt bb hbb
  rw [ptrEnvBefore_of_length_le hbb hle, ptrEnvBefore_zero]
  exact hedges target htgt

end MiniRustSpec.Correspondence
