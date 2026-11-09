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
# Raw pointers and references in both semantics (MR-3.1, MR-3.2)

This module collects what both semantics do with thin raw pointers (`*const T`,
`*mut T`) and safe references (`&T`, `&mut T`), as the foundation for extending
the correspondence (`step_correspondence`) across `&raw const` / `&raw mut`,
`&` / `&mut`, reborrowing (`&*p`, `&mut *p`, `&raw *p`), `CopyForDeref`, `*p`,
`Offset`, and pointer casts:

* **MiniRust's representation of thin pointers and safe references.**
  `ptrBytes addr prov` is the encoding `encode_ptr` produces for an address in
  `[0, 2^64)`: the eight little-endian address bytes, each carrying the
  fragment of the pointer's provenance at its own position. `decode_ptr` reads
  the pointer back (`decode_thinRawPtr`, `decode_refTy`). `check_value` accepts
  any in-bounds address at `PtrType::Raw` (`checkValue_thinRawPtr`) and
  additionally checks non-null, pointee alignment, and dereferenceability in
  `m.mem` at `PtrType::Ref` (`checkValue_refTy`, `checkValue_refTy_null_ub`,
  `checkValue_refTy_unaligned_ub`, `checkValue_refTy_dangling_ub`, including
  across `CastOp::Transmute` and `Statement::Validate`). A byte whose fragment
  belongs to another provenance makes the decoded pointer lose its provenance
  (`decodePtrProvenance_mixed`).
* **Anneal's model of raw pointers and references** (unstable `b076d6a3`).
  `&raw const p` / `&p` (`Frozen` on `Freeze` integer targets) and
  `&raw mut p` / `&mut p` (`Active`) push a fresh Tree Borrows root entry and
  return a pointer whose `allocId` is the entry's tag (`evalRvalue_rawPtr_local`,
  `evalRvalue_ref_local`); reborrows push a child entry linked to the parent tag
  (`rawReborrowEntry`, `refReborrowEntry`: mutable reference reborrows start
  `Reserved`, and reference reborrows first read through the parent,
  `evalRvalue_rawPtr_reborrow`, `evalRvalue_ref_reborrow`). A dereference at
  offset `0` reads or writes the entry's target local at the entry's projection
  (`needsThinPtrElemResolution = false`); a dereference read freezes overlapping
  foreign `Active` entries (`freezeDerefReadBorrowsAt`), and a dereference write
  applies the Tree Borrows write transition to every entry
  (`invalidateDerefWriteBorrows_eq_map`); `Offset(p, n)` scales the 8-byte count
  `n` by the pointee stride, bounds-checks it, and faults on `Disabled` tags
  (`evalRvalue_offset`); and `PointerExposeProvenance` returns
  `tag * 65536 + offsetBytes` (`evalRvalue_expose`).

The two models agree on creating raw pointers and references to locals, array
elements, or struct/tuple fields, on reborrowing and copying them, on reading
and writing through non-disabled tags (tracked flow-sensitively across arbitrary
CFGs by `ptrAliasingOk` / `PtrEnvOk`), on `PtrToPtr` casts, and on rejecting
reads through dangling or uninitialized pointers/references. They disagree, with
MiniRust as the ground truth, on:

1. **Dereferencing an offset pointer**: Anneal reads the original target,
   MiniRust the offset address, or raises UB if that address is misaligned
   for the pointee type or outside the allocation.
2. **Out-of-bounds and overflowing `Offset`**: MiniRust's `ptr_offset_inbounds`
   (after `MulUnchecked`) raises UB; Anneal continues.
3. **Exposed addresses**: Anneal's address encodes the borrow tag, so two
   pointers to the same local expose different integers; MiniRust exposes the
   allocation's address.
4. **Aliasing**: Anneal's Tree Borrows entries make a write through a `Frozen`
   pointer (including an `Active` entry frozen by a foreign read), or an access
   through a tag disabled by a foreign write, UB; `BasicMemory` has no aliasing
   model (`retag_ptr` is the identity) and accepts both. The static analysis
   disables every pointer local such an access could reach (`stepDerefWrite`,
   `stepForeignRead`; soundness `PtrEnvOk.foreignRead`, `PtrEnvOk.derefRead`).

In 1-3 Anneal's semantics accepts executions that MiniRust rejects or runs
differently, so a correspondence covering them would be false; in 4 Anneal is
merely stricter, and `ptrAliasingOk` tracks tag liveness flow-sensitively across
CFGs so safe Rust borrow/reborrow patterns (mutable reborrow + write + child
use, sequential NLL borrows, and loop borrows/reborrows) stay inside
`inFragment`. `MiniRustSpec.Correspondence.PointerWitness` checks each case on
concrete programs in both semantics.
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

@[simp] theorem checkPtrMetadata_none : checkPtrMetadata none .None = .ok () := rfl

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

/-- A projection without `Index`, which Anneal's `&raw` stores as it is
(`resolveBorrowProjectionElems` rewrites only `Index` into `ConstantIndex`). -/
def noIndexProj : List ProjectionElem → Bool
  | [] => true
  | .index _ :: _ => false
  | _ :: rest => noIndexProj rest

theorem resolveBorrowProjectionElems_noIndex (locals : List LocalSlot) (proj : List ProjectionElem)
    (h : noIndexProj proj = true) : resolveBorrowProjectionElems locals proj = some proj := by
  induction proj with
  | nil => rfl
  | cons elem rest ih =>
    cases elem <;> simp_all [noIndexProj, resolveBorrowProjectionElems]

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
    (slot : LocalSlot) (hs : locals[place.local_]? = some slot) (hlive : slot ≠ .dead) :
    evalRvalue locals (.rawPtr mutbl place) mem decls layouts =
      .ok (.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8) locals
        { mem with borrows := rawPtrEntry mem.nextTag mutbl place :: mem.borrows,
                   nextTag := mem.nextTag + 1 } := by
  obtain ⟨x, proj⟩ := place
  have hres := resolveBorrowProjectionElems_noIndex locals proj hni
  cases proj with
  | nil =>
    cases slot with
    | dead => exact absurd rfl hlive
    | uninit =>
      cases mutbl <;> simp [evalRvalue, get?, hs, rawPtrEntry, rawPtrPerm, hsh]
    | init v =>
      cases mutbl <;> simp [evalRvalue, get?, hs, rawPtrEntry, rawPtrPerm, hsh]
  | cons e rest =>
    cases e with
    | deref => exact absurd rfl (hnd rest)
    | _ =>
      cases slot with
      | dead => exact absurd rfl hlive
      | uninit => cases mutbl <;> simp_all [evalRvalue, get?, rawPtrEntry, rawPtrPerm]
      | init v => cases mutbl <;> simp_all [evalRvalue, get?, rawPtrEntry, rawPtrPerm]

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

/-- The Tree Borrows permission of Anneal's `&place` (`Frozen` on `Freeze`
targets), `&mut place` (`Active`), and two-phase `&two_phase mut place`
(`Reserved`). -/
def refBorrowPerm : MirAst.BorrowKind → TreeBorrowPerm
  | .shared => .frozen
  | .mut false => .active
  | .mut true => .reserved

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
  | «mut» twoPhase =>
    cases twoPhase with
    | false => exact .inl rfl
    | true => exact .inr ⟨rfl, rfl⟩

/-- Anneal's `&place`, `&mut place`, or `&two_phase mut place` on a live local
in the fragment: for any target place with `ptrTargetSpec` (all of whose leaf
types are integer and therefore `Freeze`), `.shared` records `.frozen`,
`.mut false` records `.active`, and `.mut true` records `.reserved`, matching
`refBorrowEntry mem.nextTag bkind place`. -/
theorem evalRvalue_ref_local (locals : List LocalSlot) (bkind : MirAst.BorrowKind)
    (place : Place)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec layouts decls place = some (pointeeIt, relOff))
    (hnd : ∀ rest, place.projection ≠ .deref :: rest) (hni : noIndexProj place.projection = true)
    (slot : LocalSlot) (hs : locals[place.local_]? = some slot) (hlive : slot ≠ .dead) :
    evalRvalue locals (.ref bkind place) mem decls layouts =
      .ok (.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8) locals
        { mem with borrows := refBorrowEntry mem.nextTag bkind place :: mem.borrows,
                   nextTag := mem.nextTag + 1 } := by
  have hsh := sharedBorrowPerm_of_ptrTargetSpec hspec
  obtain ⟨x, proj⟩ := place
  have hres := resolveBorrowProjectionElems_noIndex locals proj hni
  cases bkind with
  | shared =>
    cases proj with
    | nil =>
      cases slot with
      | dead => exact absurd rfl hlive
      | uninit => simp [evalRvalue, get?, hs, refBorrowEntry, refBorrowPerm, hsh]
      | init v => simp [evalRvalue, get?, hs, refBorrowEntry, refBorrowPerm, hsh]
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
      | uninit => simp [evalRvalue, get?, hs, refBorrowEntry, refBorrowPerm]
      | init v => simp [evalRvalue, get?, hs, refBorrowEntry, refBorrowPerm]
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
  | .not, .reserved => .reserved
  | .not, _ => .frozen
  | .mut, _ => .active

/-- Anneal's Tree Borrows entry for a raw reborrow `&raw mutbl *_p` through the
parent entry `parent` named by `parentTag`: a child of `parentTag` on the
parent's target place and byte range. -/
def rawReborrowEntry (tag : Nat) (mutbl : MirAst.Mutability) (parent : BorrowEntry)
    (parentTag : Nat) : BorrowEntry :=
  { tag := tag, targetLocal := parent.targetLocal, targetProjection := parent.targetProjection,
    perm := rawReborrowPerm mutbl parent.perm, rangeOffset := parent.rangeOffset,
    rangeLen := parent.rangeLen, parentTag := some parentTag }

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
    rangeLen := parent.rangeLen, parentTag := some parentTag }

/-- Anneal's reborrow `&raw const *_p` / `&raw mut *_p` through an initialized
pointer or reference local `_p` to an integer whose entry `parentEntry` has
compatible permission (`.active` or `.reserved` for `&raw mut`) and needs no
thin-pointer element resolution (`needsThinPtrElemResolution = false`, e.g. at
offset `0` on a `ptrTargetSpec` target): pushes the child entry
`rawReborrowEntry` without accessing the target (no initial read). -/
theorem evalRvalue_rawPtr_reborrow (locals : List LocalSlot) (mutbl : MirAst.Mutability)
    (p : Nat) (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (dp : LocalDecl) (srcMutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (hdp : decls[p]? = some dp) (hp_ty : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt))
    (parentPtr : ProvenancePtr) (hp : locals[p]? = some (.init (.ptr parentPtr 8)))
    (parentEntry : BorrowEntry) (he : lookupBorrow mem.borrows parentPtr.tag = some parentEntry)
    (hndis : parentEntry.perm ≠ .disabled)
    (hmut : mutbl = .mut → parentEntry.perm = .active ∨ parentEntry.perm = .reserved)
    (hthin : needsThinPtrElemResolution parentEntry.targetProjection parentPtr.offsetBytes =
      false) :
    evalRvalue locals (.rawPtr mutbl ⟨p, [.deref]⟩) mem decls layouts =
      .ok (.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8) locals
        { mem with
          borrows := rawReborrowEntry mem.nextTag mutbl parentEntry parentPtr.tag :: mem.borrows,
          nextTag := mem.nextTag + 1 } := by
  have hsh : sharedBorrowPerm decls layouts ⟨p, [.deref]⟩ = .frozen :=
    sharedBorrowPerm_of_deref_ptrPointeeOf hdp hp_ty
  cases mutbl with
  | not =>
    cases htp : parentEntry.targetProjection with
    | nil =>
      rw [htp] at hthin
      cases hpe : parentEntry.perm with
      | disabled => exact absurd hpe hndis
      | _ => simp [evalRvalue, get?, hp, he, hpe, htp, hsh, rawReborrowEntry, rawReborrowPerm]
    | cons ph pt =>
      rw [htp] at hthin
      cases hpe : parentEntry.perm with
      | disabled => exact absurd hpe hndis
      | _ =>
        simp [evalRvalue, get?, hp, he, hpe, htp, hthin, hsh,
          appendProjections_nil_right, rawReborrowEntry, rawReborrowPerm]
  | «mut» =>
    rcases hmut rfl with hpe | hpe <;>
    (cases htp : parentEntry.targetProjection with
    | nil =>
      simp [evalRvalue, get?, hp, he, hpe, htp, rawReborrowEntry, rawReborrowPerm]
    | cons ph pt =>
      rw [htp] at hthin
      simp [evalRvalue, get?, hp, he, hpe, htp, hthin,
        appendProjections_nil_right, rawReborrowEntry, rawReborrowPerm])

/-- Anneal's reborrow `&*_p` / `&mut *_p` / `&two_phase mut *_p` through an
initialized pointer or reference local `_p` to an integer whose entry
`parentEntry` has compatible permission (`.active` or `.reserved` for mutable
reborrows) and needs no thin-pointer element resolution: performs the initial
read through `_p`'s tag (`freezeTreeBorrowsOnReadAtProj`, freezing foreign
`.active` entries overlapping the parent's target,
`PermissionUnprot::init_access`) and pushes the child entry `refReborrowEntry`. -/
theorem evalRvalue_ref_reborrow (locals : List LocalSlot) (bkind : MirAst.BorrowKind)
    (p : Nat)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (dp : LocalDecl) (srcMutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (hdp : decls[p]? = some dp) (hp_ty : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt))
    (parentPtr : ProvenancePtr) (hp : locals[p]? = some (.init (.ptr parentPtr 8)))
    (parentEntry : BorrowEntry) (he : lookupBorrow mem.borrows parentPtr.tag = some parentEntry)
    (hndis : parentEntry.perm ≠ .disabled)
    (hmut : borrowKindMutbl bkind = .mut → parentEntry.perm = .active ∨ parentEntry.perm = .reserved)
    (hthin : needsThinPtrElemResolution parentEntry.targetProjection parentPtr.offsetBytes =
      false) :
    evalRvalue locals (.ref bkind ⟨p, [.deref]⟩) mem decls layouts =
      .ok (.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8) locals
        { mem with
          borrows := refReborrowEntry mem.nextTag bkind parentEntry parentPtr.tag ::
            MirSemantics.freezeTreeBorrowsOnReadAtProj mem.borrows mem.borrows
              parentEntry.targetLocal (some parentPtr.tag) parentEntry.targetProjection
              parentEntry.rangeOffset parentEntry.rangeLen,
          nextTag := mem.nextTag + 1 } := by
  have hsh : sharedBorrowPerm decls layouts ⟨p, [.deref]⟩ = .frozen :=
    sharedBorrowPerm_of_deref_ptrPointeeOf hdp hp_ty
  cases bkind with
  | shared =>
    cases htp : parentEntry.targetProjection with
    | nil =>
      rw [htp] at hthin
      cases hpe : parentEntry.perm with
      | disabled => exact absurd hpe hndis
      | _ =>
        simp [evalRvalue, get?, hp, he, hpe, htp, hsh, refReborrowEntry, refReborrowPerm]
    | cons ph pt =>
      rw [htp] at hthin
      cases hpe : parentEntry.perm with
      | disabled => exact absurd hpe hndis
      | _ =>
        simp [evalRvalue, get?, hp, he, hpe, htp, hthin, hsh,
          appendProjections_nil_right, refReborrowEntry, refReborrowPerm]
  | «mut» twoPhase =>
    rcases hmut rfl with hpe | hpe <;>
    cases twoPhase <;>
    (cases htp : parentEntry.targetProjection with
    | nil =>
      simp [evalRvalue, get?, hp, he, hpe, htp, refReborrowEntry, refReborrowPerm]
    | cons ph pt =>
      rw [htp] at hthin
      simp [evalRvalue, get?, hp, he, hpe, htp, hthin,
        appendProjections_nil_right, refReborrowEntry, refReborrowPerm])

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
    (hdst : ptrPointeeOf castTy = some (dstMutbl, dstIt)) :
    (∀ pv, pv.offsetBytes = 0 → locals[p]? = some (.init (.ptr pv 8)) →
      evalRvalue locals (.cast .transmute (.copy ⟨p, []⟩) castTy) mem decls layouts =
        .ok (.ptr pv 8) locals mem) ∧
    ((locals[p]? = some .uninit ∨ locals[p]? = some .dead) →
      evalRvalue locals (.cast .transmute (.copy ⟨p, []⟩) castTy) mem decls layouts = .ub) := by
  refine ⟨fun pv hoff hpv => ?_, fun hu => ?_⟩
  · have hszSrc := rigidTyByteSize_of_ptrPointeeOf layouts hsrc
    have hszDst := rigidTyByteSize_of_ptrPointeeOf layouts hdst
    have hopTy : MirSemantics.operandTy decls layouts (.copy ⟨p, []⟩) = some dp.ty := by
      simp [MirSemantics.operandTy, MirSemantics.placeTy, MirSemantics.resolveProjectedTy, get?, hdp]
    have henc := encodeValueToBytes_of_ptrPointeeOf layouts hsrc pv hoff
    obtain ⟨bs, hbs⟩ : ∃ bs, MirSemantics.encodeScalarBytes ⟨0, 8⟩ (.some (pv.allocId, pv.tag)) = some bs :=
      ⟨_, rfl⟩
    rw [hbs] at henc
    obtain ⟨hdec, hlen⟩ := decodeValueFromBytes_of_ptrPointeeOf layouts hdst pv hoff hbs
    have hlenEq : Nat.beq (Trusted.Sequence.length bs) 8 = true := by
      have : Trusted.Sequence.length bs = bs.length := rfl
      simp [this, hlen]
    simp [evalRvalue, evalByteCast, evalOperand, get?, hpv, readProjectedValue,
      hszDst, hopTy, hszSrc, henc, hlenEq, hdec]
  · rcases hu with hu | hu <;>
      simp [evalRvalue, evalByteCast, evalOperand, get?, hu]

/-- Reborrowing a `Frozen` pointer or reference as `&mut *_p` is UB in Anneal's
Tree Borrows model. -/
theorem evalRvalue_ref_reborrow_frozen_mut_ub (locals : List LocalSlot) (twoPhase : Bool)
    (p : Nat) ( restProj : List ProjectionElem)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (parentPtr : ProvenancePtr) (sz : Nat) (hp : locals[p]? = some (.init (.ptr parentPtr sz)))
    (parentEntry : BorrowEntry) (he : lookupBorrow mem.borrows parentPtr.tag = some parentEntry)
    (hfr : parentEntry.perm = .frozen) :
    evalRvalue locals (.ref (.mut twoPhase) ⟨p, .deref :: restProj⟩) mem decls layouts = .ub := by
  simp [evalRvalue, get?, hp, he, hfr]

/-- Reborrowing a `Disabled` pointer or reference as `&*_p` or `&mut *_p` is UB
in Anneal's Tree Borrows model. -/
theorem evalRvalue_ref_reborrow_disabled_ub (locals : List LocalSlot) (bkind : MirAst.BorrowKind)
    (p : Nat) (restProj : List ProjectionElem)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (parentPtr : ProvenancePtr) (sz : Nat) (hp : locals[p]? = some (.init (.ptr parentPtr sz)))
    (parentEntry : BorrowEntry) (he : lookupBorrow mem.borrows parentPtr.tag = some parentEntry)
    (hdis : parentEntry.perm = .disabled) :
    evalRvalue locals (.ref bkind ⟨p, .deref :: restProj⟩) mem decls layouts = .ub := by
  simp [evalRvalue, get?, hp, he, hdis]

/-- Reborrowing a `Frozen` pointer or reference as `&raw mut *_p` is UB in
Anneal's Tree Borrows model. -/
theorem evalRvalue_rawPtr_reborrow_frozen_mut_ub (locals : List LocalSlot)
    (p : Nat) (restProj : List ProjectionElem)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (parentPtr : ProvenancePtr) (sz : Nat) (hp : locals[p]? = some (.init (.ptr parentPtr sz)))
    (parentEntry : BorrowEntry) (he : lookupBorrow mem.borrows parentPtr.tag = some parentEntry)
    (hfr : parentEntry.perm = .frozen) :
    evalRvalue locals (.rawPtr .mut ⟨p, .deref :: restProj⟩) mem decls layouts = .ub := by
  simp [evalRvalue, get?, hp, he, hfr]

/-- Reborrowing a `Disabled` pointer or reference as `&raw const *_p` or
`&raw mut *_p` is UB in Anneal's Tree Borrows model. -/
theorem evalRvalue_rawPtr_reborrow_disabled_ub (locals : List LocalSlot) (mutbl : MirAst.Mutability)
    (p : Nat) (restProj : List ProjectionElem)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (parentPtr : ProvenancePtr) (sz : Nat) (hp : locals[p]? = some (.init (.ptr parentPtr sz)))
    (parentEntry : BorrowEntry) (he : lookupBorrow mem.borrows parentPtr.tag = some parentEntry)
    (hdis : parentEntry.perm = .disabled) :
    evalRvalue locals (.rawPtr mutbl ⟨p, .deref :: restProj⟩) mem decls layouts = .ub := by
  simp [evalRvalue, get?, hp, he, hdis]

/-- Reborrowing an uninitialized or dead pointer/reference local `_p` is UB in
Anneal. -/
theorem evalRvalue_reborrow_ub_of_not_init (locals : List LocalSlot) (p : Nat)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (h : locals[p]? = some .uninit ∨ locals[p]? = some .dead) :
    (∀ mutbl, evalRvalue locals (.rawPtr mutbl ⟨p, [.deref]⟩) mem decls layouts = .ub) ∧
    (∀ bkind, evalRvalue locals (.ref bkind ⟨p, [.deref]⟩) mem decls layouts = .ub) := by
  rcases h with hu | hd
  · exact ⟨fun _ => by simp [evalRvalue, get?, hu], fun _ => by simp [evalRvalue, get?, hu]⟩
  · exact ⟨fun _ => by simp [evalRvalue, get?, hd], fun _ => by simp [evalRvalue, get?, hd]⟩

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
    (hl : evalOperand locals l mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr ptrVal sz) locals₁)
    (sc : ScalarInt) (locals₂ : List LocalSlot)
    (hr : evalOperand locals₁ r mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar sc) locals₂) :
    evalRvalue locals (.binaryOp .offset l r) mem decls layouts =
      MirSemantics.evalPtrOffsetBinOp locals₂ mem decls layouts l ptrVal sz sc := by
  simp only [evalRvalue, hl, hr]

/-- Anneal's `PtrToPtr` cast between thin raw pointers to integers keeps the
pointer, tag and offset included (no array-to-element derivation applies);
`minimize` translates a cast between thin raw pointers to its operand. -/
theorem evalRvalue_ptrToPtr (locals : List LocalSlot) (op : Operand) (ty : Ty)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (ptrVal : ProvenancePtr) (sz : Nat) (locals' : List LocalSlot)
    (h : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr ptrVal sz) locals')
    {dstMutbl : MirAst.Mutability} {dstIt : Gen.IntType}
    (hdst : rawPtrPointeeOf ty = some (dstMutbl, dstIt))
    (hsrc : ∀ srcTy, MirSemantics.operandTy decls layouts op = some srcTy →
      (ptrPointeeOf srcTy).isSome = true) :
    evalRvalue locals (.cast .ptrToPtr op ty) mem decls layouts = .ok (.ptr ptrVal sz) locals' mem := by
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
    cases elem <;> simp_all [evalRvalue, intTyBytes]
  | some srcTy =>
    have hs := hsrc srcTy hty
    rcases srcTy with ⟨sk, sl⟩
    cases sk <;> simp [ptrPointeeOf] at hs
    all_goals
      rename_i m' inner
      cases inner <;> simp [intTyBytes] at hs <;>
        cases elem <;> simp_all [evalRvalue, intTyBytes]

/-- Anneal's `PointerExposeProvenance` cast (`p as usize`, `p.expose_provenance()`)
returns `tag * 65536 + offsetBytes`, an encoding of the borrow tag rather than
an address; MiniRust's `PointerExposeProvenance` intrinsic returns the
pointer's address. -/
theorem evalRvalue_expose (locals : List LocalSlot) (op : Operand) (ty : Ty)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (ptrVal : ProvenancePtr) (sz : Nat) (locals' : List LocalSlot)
    (h : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr ptrVal sz) locals') :
    evalRvalue locals (.cast .pointerExposeProvenance op ty) mem decls layouts =
      .ok (.scalar ⟨ptrVal.allocId * 65536 + ptrVal.offsetBytes, 8⟩) locals' mem := by
  simp [evalRvalue, h]

/-- Anneal's `PointerWithExposedProvenance` cast (`n as *const T`,
`ptr::with_exposed_provenance(n)`) deterministically decodes the tag
`n / 65536` and the offset `n % 65536`; MiniRust's
`PointerWithExposedProvenance` intrinsic keeps the address `n` and predicts an
exposed provenance angelically (`int2ptrProvenance`). -/
theorem evalRvalue_withExposed (locals : List LocalSlot) (op : Operand) (ty : Ty)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (sc : ScalarInt) (locals' : List LocalSlot)
    (h : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar sc) locals') :
    evalRvalue locals (.cast .pointerWithExposedProvenance op ty) mem decls layouts =
      .ok (.ptr { allocId := sc.bits / 65536, offsetBytes := sc.bits % 65536 } 8) locals' mem := by
  simp [evalRvalue, h]
  exact ⟨rfl, rfl⟩

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
    (writerTag : Option Nat) (writeProj : List ProjectionElem) (off len : Nat) :
    (updateBorrowPermAtProj e targetLocal writerTag writeProj off len).tag = e.tag ∧
    (updateBorrowPermAtProj e targetLocal writerTag writeProj off len).targetLocal = e.targetLocal ∧
    (updateBorrowPermAtProj e targetLocal writerTag writeProj off len).targetProjection = e.targetProjection ∧
    (updateBorrowPermAtProj e targetLocal writerTag writeProj off len).protector = e.protector ∧
    (updateBorrowPermAtProj e targetLocal writerTag writeProj off len).rangeOffset = e.rangeOffset ∧
    (updateBorrowPermAtProj e targetLocal writerTag writeProj off len).rangeLen = e.rangeLen := by
  unfold updateBorrowPermAtProj
  cases Nat.beq e.targetLocal targetLocal
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases writerTag with
    | none =>
      dsimp only []
      cases borrowEntryOverlapsWrite e writeProj off len <;>
        cases e.perm <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | some tag =>
      dsimp only []
      cases Nat.beq e.tag tag <;>
        cases borrowEntryOverlapsWrite e writeProj off len <;>
        cases e.perm <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem updateBorrowPermAtProj_cases (e : BorrowEntry)
    (targetLocal tag : Nat) (writeProj : List ProjectionElem) :
    updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 = e ∨
    (e.perm = .reserved ∧
      updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 = { e with perm := .active }) ∨
    updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 = { e with perm := .disabled } := by
  unfold updateBorrowPermAtProj
  dsimp only []
  cases Nat.beq e.targetLocal targetLocal
  · exact .inl rfl
  · dsimp only []
    cases Nat.beq e.tag tag
    · dsimp only []
      cases borrowEntryOverlapsWrite e writeProj 0 0
      · exact .inl rfl
      · exact .inr (.inr rfl)
    · dsimp only []
      cases hpe : e.perm with
      | reserved => exact .inr (.inl ⟨rfl, rfl⟩)
      | _ => exact .inl rfl

theorem updateBorrowPermAtProj_cases_of_ne_reserved {e : BorrowEntry} (hnr : e.perm ≠ .reserved)
    (targetLocal tag : Nat) (writeProj : List ProjectionElem) :
    updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 = e ∨
    updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 = { e with perm := .disabled } := by
  rcases updateBorrowPermAtProj_cases e targetLocal tag writeProj with h | ⟨hr, _⟩ | h
  · exact .inl h
  · exact absurd hr hnr
  · exact .inr h

theorem updateBorrowPermAtProj_self_or_disjoint_keep (e : BorrowEntry) (targetLocal tag : Nat)
    (writeProj : List ProjectionElem)
    (h : e.targetLocal = targetLocal →
      e.tag = tag ∨
      (e.tag ≠ tag ∧ MirSemantics.projectionsOverlap e.targetProjection writeProj = false)) :
    updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 = e ∨
    updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 = { e with perm := .active } := by
  unfold updateBorrowPermAtProj
  cases hloc : Nat.beq e.targetLocal targetLocal with
  | false => exact .inl rfl
  | true =>
    rcases h (Nat.beq_eq.mp hloc) with heqTag | ⟨hneTag, hdisj⟩
    · have htag : Nat.beq e.tag tag = true := Nat.beq_eq.mpr heqTag
      simp only [htag]
      cases e.perm with
      | reserved => exact .inr rfl
      | _ => exact .inl rfl
    · have htag : Nat.beq e.tag tag = false := by
        cases hb : Nat.beq e.tag tag with
        | false => rfl
        | true => exact False.elim (hneTag (Nat.beq_eq.mp hb))
      have hov : borrowEntryOverlapsWrite e writeProj 0 0 = false := by
        simpa [borrowEntryOverlapsWrite] using hdisj
      simp [htag, hov]

theorem updateBorrowPermAtProj_nil_eq (e : BorrowEntry) (targetLocal : Nat)
    (writerTag : Option Nat) :
    updateBorrowPermAtProj e targetLocal writerTag [] 0 0 =
      updateBorrowPerm e targetLocal writerTag := by
  have hov : borrowEntryOverlapsWrite e [] 0 0 = true := by
    simpa [borrowEntryOverlapsWrite] using projectionsOverlap_nil_right e.targetProjection
  unfold updateBorrowPermAtProj updateBorrowPerm
  rw [hov]

theorem invalidateConflictingBorrows_eq_map (borrows : List BorrowEntry)
    (targetLocal : Nat) (writerTag : Option Nat) :
    invalidateConflictingBorrows borrows targetLocal writerTag =
      borrows.map (fun e => updateBorrowPermAtProj e targetLocal writerTag [] 0 0) := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    rw [invalidateConflictingBorrows_cons, ← updateBorrowPermAtProj_nil_eq, ih]
    rfl

theorem invalidateConflictingBorrowsAtProj_eq_map (borrows : List BorrowEntry)
    (targetLocal : Nat) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (off len : Nat) :
    invalidateConflictingBorrowsAtProj borrows targetLocal writerTag writeProj off len =
      borrows.map (fun e => updateBorrowPermAtProj e targetLocal writerTag writeProj off len) := by
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

theorem updateBorrowPerm_self_or_other (e : BorrowEntry) (targetLocal tag : Nat)
    (h : e.targetLocal = targetLocal → e.tag = tag ∧ e.perm ≠ .reserved) :
    updateBorrowPerm e targetLocal (some tag) = e := by
  unfold updateBorrowPerm
  cases hloc : Nat.beq e.targetLocal targetLocal with
  | false => rfl
  | true =>
    obtain ⟨heqTag, _⟩ := h (Nat.beq_eq.mp hloc)
    have htag : Nat.beq e.tag tag = true := Nat.beq_eq.mpr heqTag
    simp only [htag]

theorem invalidateConflictingBorrows_self (borrows : List BorrowEntry) (targetLocal tag : Nat)
    (h : ∀ e ∈ borrows, e.targetLocal = targetLocal → e.tag = tag ∧ e.perm ≠ .reserved) :
    invalidateConflictingBorrows borrows targetLocal (some tag) = borrows := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    rw [invalidateConflictingBorrows_cons,
      updateBorrowPerm_self_or_other e targetLocal tag (h e (by simp)),
      ih (fun e' he' => h e' (by simp [he']))]

theorem updateBorrowPermAtProj_self_or_disjoint (e : BorrowEntry) (targetLocal tag : Nat)
    (writeProj : List ProjectionElem)
    (h : e.targetLocal = targetLocal →
      (e.tag = tag ∧ e.perm ≠ .reserved) ∨
      (e.tag ≠ tag ∧ MirSemantics.projectionsOverlap e.targetProjection writeProj = false)) :
    updateBorrowPermAtProj e targetLocal (some tag) writeProj 0 0 = e := by
  unfold updateBorrowPermAtProj
  cases hloc : Nat.beq e.targetLocal targetLocal with
  | false => rfl
  | true =>
    rcases h (Nat.beq_eq.mp hloc) with ⟨heqTag, _⟩ | ⟨hneTag, hdisj⟩
    · have htag : Nat.beq e.tag tag = true := Nat.beq_eq.mpr heqTag
      simp only [htag]
    · have htag : Nat.beq e.tag tag = false := by
        cases hb : Nat.beq e.tag tag with
        | false => rfl
        | true => exact False.elim (hneTag (Nat.beq_eq.mp hb))
      have hov : borrowEntryOverlapsWrite e writeProj 0 0 = false := by
        simpa [borrowEntryOverlapsWrite] using hdisj
      simp [htag, hov]

theorem invalidateConflictingBorrowsAtProj_self_or_disjoint (borrows : List BorrowEntry)
    (targetLocal tag : Nat) (writeProj : List ProjectionElem)
    (h : ∀ e ∈ borrows, e.targetLocal = targetLocal →
      (e.tag = tag ∧ e.perm ≠ .reserved) ∨
      (e.tag ≠ tag ∧ MirSemantics.projectionsOverlap e.targetProjection writeProj = false)) :
    invalidateConflictingBorrowsAtProj borrows targetLocal (some tag) writeProj 0 0 = borrows := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    simp only [invalidateConflictingBorrowsAtProj,
      updateBorrowPermAtProj_self_or_disjoint e targetLocal tag writeProj (h e (by simp)),
      ih (fun e' he' => h e' (by simp [he']))]

/-- The Tree Borrows write transition of a write through tag `tag` keeps every
entry that shares `tag` (local write: `.reserved` activates) or whose target is
disjoint from the write (any writer). -/
theorem updateBorrowPermTreeAtProj_self_or_disjoint_keep (all : List BorrowEntry)
    (e : BorrowEntry) (targetLocal tag : Nat) (writeProj : List ProjectionElem)
    (h : e.targetLocal = targetLocal →
      e.tag = tag ∨
      (e.tag ≠ tag ∧ MirSemantics.projectionsOverlap e.targetProjection writeProj = false)) :
    MirSemantics.updateBorrowPermTreeAtProj all e targetLocal (some tag) writeProj 0 0 = e ∨
    MirSemantics.updateBorrowPermTreeAtProj all e targetLocal (some tag) writeProj 0 0 =
      { e with perm := .active } := by
  unfold MirSemantics.updateBorrowPermTreeAtProj MirSemantics.resolveTreeBorrowWriterTag
  dsimp only
  cases MirSemantics.isBorrowDescendantOrSelf all tag e.tag with
  | false => exact updateBorrowPermAtProj_self_or_disjoint_keep e targetLocal tag writeProj h
  | true =>
    exact updateBorrowPermAtProj_self_or_disjoint_keep e targetLocal e.tag writeProj
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
          entry.targetProjection 0 0) := by
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
    exact invalidateTreeBorrowsAtProj_eq_map _ _ _ _ _ _ _

theorem invalidateDerefWriteBorrows_noop (locals : List LocalSlot) (borrows : List BorrowEntry)
    (p : Nat) (ptrVal : ProvenancePtr) (entry : BorrowEntry)
    (hp : locals[p]? = some (.init (.ptr ptrVal 8)))
    (he : lookupBorrow borrows ptrVal.tag = some entry)
    (hrlen : entry.rangeLen = 0) (hroff : entry.rangeOffset = 0)
    (hfull : MirSemantics.resolveDerefWriteFullProj locals locals (.ptr ptrVal 8) entry [] =
      entry.targetProjection)
    (hdisj : ∀ e ∈ borrows, e.targetLocal = entry.targetLocal →
      (e.tag = ptrVal.tag ∧ e.perm ≠ .reserved) ∨
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
        entry.targetProjection (fun _ => .inl ⟨rfl, hnr⟩)
    · simp only [hnd]
      have hne : e.tag ≠ ptrVal.tag := by
        intro h
        rw [h, isBorrowDescendantOrSelf_self] at hnd
        cases hnd
      exact updateBorrowPermAtProj_self_or_disjoint e entry.targetLocal ptrVal.tag
        entry.targetProjection (fun _ => .inr ⟨hne, hov⟩)
  · cases hd : MirSemantics.isBorrowDescendantOrSelf borrows ptrVal.tag e.tag
    · simp only [hd]
      exact updateBorrowPermAtProj_self_or_disjoint e entry.targetLocal ptrVal.tag
        entry.targetProjection (fun hl => absurd hl hloc)
    · simp only [hd]
      exact updateBorrowPermAtProj_self_or_disjoint e entry.targetLocal e.tag
        entry.targetProjection (fun hl => absurd hl hloc)

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
  rcases h with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
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

/-- Concrete meaning of `PtrLocalState` for local `p` at runtime slots `view`
and Anneal borrow table `borrows`:
* `.empty` (`⊥`): `p` holds no initialized 8-byte pointer;
* `.live target peers`: if `p` holds an initialized pointer `pv`, its borrow
  entry is not `.disabled`, is not `.frozen` when `p` is a mutable
  pointer/reference local (`isMutPtrLocal`; Tree Borrows foreign reads freeze
  `.active` entries, `stepForeignRead`), matches `target` (when `some`), and
  shares `pv.tag` with every initialized pointer/reference local in `peers`;
* `.disabled` (`⊤`): unconstrained (`True`). -/
def PtrLocalOk (body : CapturedMir) (view : List LocalSlot) (borrows : List BorrowEntry)
    (p : Nat) : PtrLocalState → Prop
  | .empty =>
    ∀ dp pv, body.localDecls[p]? = some dp → isPtrTy dp.ty = true →
      view[p]? ≠ some (.init (.ptr pv 8))
  | .live target peers =>
    ∀ dp pv, body.localDecls[p]? = some dp → isPtrTy dp.ty = true →
      view[p]? = some (.init (.ptr pv 8)) →
      (∃ entry, lookupBorrow borrows pv.tag = some entry ∧ entry.perm ≠ .disabled ∧
        (isMutPtrLocal body.localDecls p = true → entry.perm ≠ .frozen) ∧
        (∀ q, target = some q → (entry.targetLocal, borrowProjSteps entry.targetProjection) = q)) ∧
      (∀ r ∈ peers, ∀ dr pv_r, body.localDecls[r]? = some dr → isPtrTy dr.ty = true →
        view[r]? = some (.init (.ptr pv_r 8)) → pv_r.tag = pv.tag)
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
  | live _ _ =>
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
  | live t1 ps1 =>
    cases s2 with
    | empty => simp [subsumesPtrLocalState] at hsub
    | disabled => trivial
    | live t2 ps2 =>
      simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
        List.contains_iff_mem] at hsub
      obtain ⟨ht, hps⟩ := hsub
      intro dp pv hdp hpty hv
      obtain ⟨⟨entry, hlk, hndis, hnf, ht1⟩, hpeers1⟩ := hok dp pv hdp hpty hv
      refine ⟨⟨entry, hlk, hndis, hnf, fun q hq => ?_⟩, fun r hr dr pv_r hdr hptr hvr =>
        hpeers1 r (hps r hr) dr pv_r hdr hptr hvr⟩
      rw [hq] at ht
      simp only [decide_eq_true_eq] at ht
      exact ht1 q ht

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

/-! ### `PtrLocalState` join-semilattice, monotonicity, finite-fuel convergence, and least fixed point -/

theorem subsumesPtrLocalState_refl (s : PtrLocalState) :
    subsumesPtrLocalState s s = true := by
  cases s with
  | empty | disabled => rfl
  | live t ps =>
    cases t <;> simp [subsumesPtrLocalState]

theorem subsumesPtrLocalState_disabled_right (s : PtrLocalState) :
    subsumesPtrLocalState s .disabled = true := by
  cases s <;> rfl

theorem subsumesPtrLocalState_trans {s1 s2 s3 : PtrLocalState}
    (h12 : subsumesPtrLocalState s1 s2 = true)
    (h23 : subsumesPtrLocalState s2 s3 = true) :
    subsumesPtrLocalState s1 s3 = true := by
  cases s1 with
  | empty => rfl
  | disabled =>
    cases s2 <;> cases s3 <;> simp_all [subsumesPtrLocalState]
  | live t1 ps1 =>
    cases s2 with
    | empty => simp [subsumesPtrLocalState] at h12
    | disabled =>
      cases s3 <;> simp_all [subsumesPtrLocalState]
    | live t2 ps2 =>
      cases s3 with
      | empty => simp [subsumesPtrLocalState] at h23
      | disabled => rfl
      | live t3 ps3 =>
        simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
          List.contains_iff_mem] at h12 h23 ⊢
        refine ⟨?_, fun r hr => h12.2 r (h23.2 r hr)⟩
        cases t3 with
        | none => trivial
        | some q3 =>
          simp only [decide_eq_true_eq] at h23 ⊢
          rw [h23.1] at h12
          simpa using h12.1

theorem joinPtrLocalState_subsumes_left (s1 s2 : PtrLocalState) :
    subsumesPtrLocalState s1 (joinPtrLocalState s1 s2) = true := by
  cases s1 with
  | empty => rfl
  | disabled => cases s2 <;> rfl
  | live t1 ps1 =>
    cases s2 with
    | empty => exact subsumesPtrLocalState_refl _
    | disabled => rfl
    | live t2 ps2 =>
      simp only [joinPtrLocalState, subsumesPtrLocalState, Bool.and_eq_true,
        List.all_eq_true, List.mem_filter, List.contains_iff_mem]
      refine ⟨?_, fun r hr => hr.1⟩
      by_cases h : (t1 == t2) = true
      · simp only [h, ↓reduceIte]
        cases t1 <;> simp
      · simp [h]

theorem joinPtrLocalState_subsumes_right (s1 s2 : PtrLocalState) :
    subsumesPtrLocalState s2 (joinPtrLocalState s1 s2) = true := by
  cases s1 with
  | empty => exact subsumesPtrLocalState_refl _
  | disabled => cases s2 <;> rfl
  | live t1 ps1 =>
    cases s2 with
    | empty => rfl
    | disabled => rfl
    | live t2 ps2 =>
      simp only [joinPtrLocalState, subsumesPtrLocalState, Bool.and_eq_true,
        List.all_eq_true, List.mem_filter, List.contains_iff_mem]
      refine ⟨?_, fun r hr => hr.2⟩
      by_cases h : (t1 == t2) = true
      · have heq : t1 = t2 := eq_of_beq h
        subst heq
        simp only [h, ↓reduceIte]
        cases t1 <;> simp
      · simp [h]

theorem joinPtrLocalState_least {s1 s2 u : PtrLocalState}
    (h1 : subsumesPtrLocalState s1 u = true)
    (h2 : subsumesPtrLocalState s2 u = true) :
    subsumesPtrLocalState (joinPtrLocalState s1 s2) u = true := by
  cases s1 with
  | empty => exact h2
  | disabled =>
    cases s2 <;> cases u <;> simp_all [joinPtrLocalState, subsumesPtrLocalState]
  | live t1 ps1 =>
    cases s2 with
    | empty => exact h1
    | disabled =>
      cases u <;> simp_all [joinPtrLocalState, subsumesPtrLocalState]
    | live t2 ps2 =>
      cases u with
      | empty => simp [subsumesPtrLocalState] at h1
      | disabled => rfl
      | live tu psu =>
        simp only [joinPtrLocalState, subsumesPtrLocalState, Bool.and_eq_true,
          List.all_eq_true, List.mem_filter, List.contains_iff_mem] at h1 h2 ⊢
        refine ⟨?_, fun r hr => ⟨h1.2 r hr, h2.2 r hr⟩⟩
        cases tu with
        | none => trivial
        | some qu =>
          simp only [decide_eq_true_eq] at h1 h2 ⊢
          rw [h1.1, h2.1]
          simp

theorem subsumesPtrEnv_refl (n : Nat) (e : List PtrLocalState) :
    subsumesPtrEnv n e e = true := by
  simp [subsumesPtrEnv, List.all_eq_true, subsumesPtrLocalState_refl]

theorem subsumesPtrEnv_trans {n : Nat} {e1 e2 e3 : List PtrLocalState}
    (h12 : subsumesPtrEnv n e1 e2 = true) (h23 : subsumesPtrEnv n e2 e3 = true) :
    subsumesPtrEnv n e1 e3 = true := by
  simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range] at h12 h23 ⊢
  exact fun q hq => subsumesPtrLocalState_trans (h12 q hq) (h23 q hq)

theorem subsumesPtrEnv_initPtrEnv (n : Nat) (e : List PtrLocalState) :
    subsumesPtrEnv n (initPtrEnv n) e = true := by
  simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
  intro q hq
  rw [initPtrEnv, getD_map_range _ _ _ hq]
  rfl

theorem joinPtrEnv_subsumes_left (n : Nat) (e1 e2 : List PtrLocalState) :
    subsumesPtrEnv n e1 (joinPtrEnv n e1 e2) = true := by
  simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
  intro q hq
  rw [joinPtrEnv, getD_map_range _ _ _ hq]
  exact joinPtrLocalState_subsumes_left _ _

theorem joinPtrEnv_subsumes_right (n : Nat) (e1 e2 : List PtrLocalState) :
    subsumesPtrEnv n e2 (joinPtrEnv n e1 e2) = true := by
  simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
  intro q hq
  rw [joinPtrEnv, getD_map_range _ _ _ hq]
  exact joinPtrLocalState_subsumes_right _ _

theorem joinPtrEnv_least {n : Nat} {e1 e2 u : List PtrLocalState}
    (h1 : subsumesPtrEnv n e1 u = true) (h2 : subsumesPtrEnv n e2 u = true) :
    subsumesPtrEnv n (joinPtrEnv n e1 e2) u = true := by
  simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range] at h1 h2 ⊢
  intro q hq
  rw [joinPtrEnv, getD_map_range _ _ _ hq]
  exact joinPtrLocalState_least (h1 q hq) (h2 q hq)

theorem subsumesPtrLocalState_getD_of_length {n : Nat} {e1 e2 : List PtrLocalState}
    (hlen1 : e1.length = n) (hlen2 : e2.length = n)
    (hsub : subsumesPtrEnv n e1 e2 = true) (p : Nat) :
    subsumesPtrLocalState (e1.getD p .disabled) (e2.getD p .disabled) = true := by
  by_cases hp : p < n
  · simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range] at hsub
    exact hsub p hp
  · have h1 : e1[p]? = none := List.getElem?_eq_none (by omega)
    have h2 : e2[p]? = none := List.getElem?_eq_none (by omega)
    simp [List.getD, h1, h2, subsumesPtrLocalState]

theorem removePeerFromState_mono (i : Nat) {s1 s2 : PtrLocalState}
    (h : subsumesPtrLocalState s1 s2 = true) :
    subsumesPtrLocalState (removePeerFromState i s1) (removePeerFromState i s2) = true := by
  cases s1 with
  | empty => rfl
  | disabled =>
    cases s2 <;> simp_all [removePeerFromState, subsumesPtrLocalState]
  | live t1 ps1 =>
    cases s2 with
    | empty => simp [subsumesPtrLocalState] at h
    | disabled => rfl
    | live t2 ps2 =>
      simp only [removePeerFromState, subsumesPtrLocalState, Bool.and_eq_true,
        List.all_eq_true, List.mem_filter, List.contains_iff_mem] at h ⊢
      exact ⟨h.1, fun r hr => ⟨h.2 r hr.1, hr.2⟩⟩

theorem addPeerToState_mono (i : Nat) {s1 s2 : PtrLocalState}
    (h : subsumesPtrLocalState s1 s2 = true) :
    subsumesPtrLocalState (addPeerToState i s1) (addPeerToState i s2) = true := by
  cases s1 with
  | empty => rfl
  | disabled =>
    cases s2 <;> simp_all [addPeerToState, subsumesPtrLocalState]
  | live t1 ps1 =>
    cases s2 with
    | empty => simp [subsumesPtrLocalState] at h
    | disabled => rfl
    | live t2 ps2 =>
      simp only [addPeerToState]
      by_cases hc2 : ps2.contains i = true
      · have hc1 : ps1.contains i = true := by
          simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
            List.contains_iff_mem] at h
          exact List.contains_iff_mem.mpr (h.2 i (List.contains_iff_mem.mp hc2))
        simp only [hc1, hc2, ↓reduceIte]
        exact h
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        by_cases hc1 : ps1.contains i = true
        · simp only [hc1, ↓reduceIte, subsumesPtrLocalState, Bool.and_eq_true,
            List.all_eq_true, List.contains_iff_mem] at h ⊢
          refine ⟨h.1, fun r hr => ?_⟩
          rcases List.mem_cons.mp hr with rfl | hr2
          · exact List.contains_iff_mem.mp hc1
          · exact h.2 r hr2
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte, subsumesPtrLocalState,
            Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h ⊢
          refine ⟨h.1, fun r hr => ?_⟩
          rcases List.mem_cons.mp hr with rfl | hr2
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem i (h.2 r hr2)

theorem ptrStmtStep_length (decls : List LocalDecl) (env : List PtrLocalState)
    (s : MirAst.Statement) :
    (ptrStmtStep decls env s).length = decls.length := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign dst rv =>
    obtain ⟨i, projs⟩ := dst
    cases projs with
    | nil =>
      simp only [ptrStmtStep]
      split
      · cases directBorrowOf rv with
        | some bp => simp [setPtrLocal]
        | none =>
          cases reborrowParentOf rv with
          | some p => simp [stepReborrow, setPtrLocal]
          | none =>
            cases ptrCopySrcOf decls rv with
            | some p =>
              simp only [stepPtrCopy]
              split <;> simp
            | none => simp [setPtrLocal]
      · cases ptrDerefReadSrc rv <;> simp [stepForeignRead]
    | cons hd tl =>
      cases hd with
      | deref =>
        cases tl with
        | nil =>
          simp only [ptrStmtStep]
          cases ptrDerefReadSrc rv <;> (simp only [stepDerefWrite]; split <;> simp)
        | cons _ _ => simp [ptrStmtStep]
      | _ => simp [ptrStmtStep]
  | storageLive i | storageDead i =>
    simp only [ptrStmtStep]
    split <;> simp [setPtrLocal]
  | deinit p =>
    obtain ⟨i, projs⟩ := p
    cases projs with
    | nil =>
      simp only [ptrStmtStep]
      split <;> simp [setPtrLocal]
    | cons _ _ => simp [ptrStmtStep]
  | _ => simp [ptrStmtStep]

private theorem stepDerefWrite_mono (n : Nat) {e1 e2 : List PtrLocalState}
    (hall : ∀ p, subsumesPtrLocalState (e1.getD p .disabled) (e2.getD p .disabled) = true)
    (w : Nat) :
    subsumesPtrEnv n (stepDerefWrite n e1 w) (stepDerefWrite n e2 w) = true := by
  simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
  intro q hq
  unfold stepDerefWrite
  have hw := hall w
  cases hw1 : e1.getD w .disabled with
  | empty =>
    rw [getD_map_range _ _ _ hq]
    cases hw2 : e2.getD w .disabled with
    | empty =>
      rw [getD_map_range _ _ _ hq]
      exact hall q
    | disabled =>
      rw [getD_map_range _ _ _ hq]
      exact subsumesPtrLocalState_disabled_right _
    | live wT2 wP2 =>
      rw [getD_map_range _ _ _ hq]
      have hq_sub := hall q
      cases hq2 : e2.getD q .disabled with
      | empty => rw [hq2] at hq_sub; exact hq_sub
      | disabled => exact subsumesPtrLocalState_disabled_right _
      | live qT2 qP2 =>
        rw [hq2] at hq_sub
        by_cases hc : (wP2.contains q || targetsDefinitelyDisjoint qT2 wT2) = true
        · simp only [hc, ↓reduceIte]; exact hq_sub
        · simp only [hc, Bool.false_eq_true, ↓reduceIte]
          exact subsumesPtrLocalState_disabled_right _
  | disabled =>
    rw [hw1] at hw
    cases hw2 : e2.getD w .disabled with
    | empty | live _ _ => rw [hw2] at hw; simp [subsumesPtrLocalState] at hw
    | disabled =>
      rw [getD_map_range _ _ _ hq]
      rfl
  | live wT1 wP1 =>
    rw [hw1] at hw
    cases hw2 : e2.getD w .disabled with
    | empty => rw [hw2] at hw; simp [subsumesPtrLocalState] at hw
    | disabled =>
      rw [getD_map_range _ _ _ hq, getD_map_range _ _ _ hq]
      exact subsumesPtrLocalState_disabled_right _
    | live wT2 wP2 =>
      rw [hw2] at hw
      simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
        List.contains_iff_mem] at hw
      rw [getD_map_range _ _ _ hq, getD_map_range _ _ _ hq]
      have hq_sub := hall q
      cases hq1 : e1.getD q .disabled with
      | empty => rfl
      | disabled =>
        rw [hq1] at hq_sub
        cases hq2 : e2.getD q .disabled with
        | empty | live _ _ => rw [hq2] at hq_sub; simp [subsumesPtrLocalState] at hq_sub
        | disabled => rfl
      | live qT1 qP1 =>
        rw [hq1] at hq_sub
        cases hq2 : e2.getD q .disabled with
        | empty => rw [hq2] at hq_sub; simp [subsumesPtrLocalState] at hq_sub
        | disabled => exact subsumesPtrLocalState_disabled_right _
        | live qT2 qP2 =>
          rw [hq2] at hq_sub
          by_cases hkeep2 : (wP2.contains q || targetsDefinitelyDisjoint qT2 wT2) = true
          · have hkeep1 : (wP1.contains q || targetsDefinitelyDisjoint qT1 wT1) = true := by
              cases hpeer : wP2.contains q with
              | true =>
                have hp1 : wP1.contains q = true :=
                  List.contains_iff_mem.mpr (hw.2 q (List.contains_iff_mem.mp hpeer))
                simp only [hp1, Bool.true_or]
              | false =>
                rw [hpeer, Bool.false_or] at hkeep2
                cases qT2 with
                | none => simp [targetsDefinitelyDisjoint] at hkeep2
                | some qp2 =>
                  cases wT2 with
                  | none => simp [targetsDefinitelyDisjoint] at hkeep2
                  | some wp2 =>
                    have hq_sub' := hq_sub
                    simp only [subsumesPtrLocalState, Bool.and_eq_true,
                      decide_eq_true_eq] at hq_sub'
                    have hw1_eq : wT1 = some wp2 := by simpa using hw.1
                    rw [hq_sub'.1, hw1_eq, hkeep2]
                    simp only [Bool.or_true]
            simp only [hkeep2, hkeep1, ↓reduceIte]
            exact hq_sub
          · simp only [hkeep2, Bool.false_eq_true, ↓reduceIte]
            exact subsumesPtrLocalState_disabled_right _

theorem stepForeignRead_getD {decls : List LocalDecl} {n : Nat} {env : List PtrLocalState}
    {r q : Nat} (hq : q < n) :
    (stepForeignRead decls n env r).getD q .disabled =
      if isMutPtrLocal decls q && !foreignReadKeeps env r q then .disabled
      else env.getD q .disabled := by
  unfold stepForeignRead
  rw [getD_map_range _ _ _ hq]

theorem stepForeignRead_getD_of_le {decls : List LocalDecl} {n : Nat} {env : List PtrLocalState}
    {r q : Nat} (hq : n ≤ q) :
    (stepForeignRead decls n env r).getD q .disabled = .disabled := by
  unfold stepForeignRead
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hq)]
  rfl

theorem stepForeignRead_length (decls : List LocalDecl) (n : Nat) (env : List PtrLocalState)
    (r : Nat) : (stepForeignRead decls n env r).length = n := by
  simp [stepForeignRead]

private theorem subsumes_live_inv {t1 : Option (Nat × List BorrowProjStep)} {ps1 : List Nat}
    {s2 : PtrLocalState} (h : subsumesPtrLocalState (.live t1 ps1) s2 = true) :
    s2 = .disabled ∨ ∃ t2 ps2, s2 = .live t2 ps2 ∧
      (∀ q2, t2 = some q2 → t1 = some q2) ∧ (∀ r ∈ ps2, r ∈ ps1) := by
  cases s2 with
  | empty => simp [subsumesPtrLocalState] at h
  | disabled => exact .inl rfl
  | live t2 ps2 =>
    right
    refine ⟨t2, ps2, rfl, fun q2 hq2 => ?_, fun r hr => ?_⟩
    · subst hq2
      simp only [subsumesPtrLocalState, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1
    · simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
        List.contains_iff_mem] at h
      exact h.2 r hr

private theorem foreignReadKeeps_mono {e1 e2 : List PtrLocalState}
    (hall : ∀ p, subsumesPtrLocalState (e1.getD p .disabled) (e2.getD p .disabled) = true)
    (r q : Nat) (h2 : foreignReadKeeps e2 r q = true) (h1 : foreignReadKeeps e1 r q = false) :
    e2.getD q .disabled = .disabled := by
  have hr := hall r
  have hq := hall q
  unfold foreignReadKeeps at h1 h2
  by_cases hqr : (q == r) = true
  · simp [hqr] at h1
  · simp only [hqr, Bool.false_or] at h1 h2
    generalize e1.getD r .disabled = a1 at hr h1
    generalize e1.getD q .disabled = b1 at hq h1
    generalize e2.getD r .disabled = a2 at hr h2
    generalize e2.getD q .disabled = b2 at hq h2 ⊢
    rcases a1 with _ | ⟨rT1, rP1⟩ | _ <;> rcases b1 with _ | ⟨qT1, qP1⟩ | _ <;>
      simp only [Bool.true_eq_false] at h1
    · -- a1 = live, b1 = live
      rcases subsumes_live_inv hq with hb2 | ⟨qT2, qP2, rfl, hqT, _⟩
      · exact hb2
      · exfalso
        rcases subsumes_live_inv hr with rfl | ⟨rT2, rP2, rfl, hrT, hrP⟩
        · simp at h2
        · simp only [Bool.or_eq_false_iff] at h1
          simp only [Bool.or_eq_true] at h2
          rcases h2 with hc | hd
          · have := hrP q (List.contains_iff_mem.mp hc)
            rw [List.contains_iff_mem.mpr this] at h1
            exact absurd h1.1 (by simp)
          · cases qT2 with
            | none => simp [targetsDefinitelyDisjoint] at hd
            | some qp2 =>
              cases rT2 with
              | none => simp [targetsDefinitelyDisjoint] at hd
              | some rp2 =>
                rw [hqT qp2 rfl, hrT rp2 rfl] at h1
                rw [hd] at h1
                exact absurd h1.2 (by simp)
    · -- a1 = disabled, b1 = live
      cases a2 with
      | empty => simp [subsumesPtrLocalState] at hr
      | live _ _ => simp [subsumesPtrLocalState] at hr
      | disabled =>
        rcases subsumes_live_inv hq with hb2 | ⟨qT2, qP2, rfl, _, _⟩
        · exact hb2
        · simp at h2

theorem stepForeignRead_mono (decls : List LocalDecl) (n : Nat) {e1 e2 : List PtrLocalState}
    (hall : ∀ p, subsumesPtrLocalState (e1.getD p .disabled) (e2.getD p .disabled) = true)
    (r : Nat) :
    ∀ p, subsumesPtrLocalState ((stepForeignRead decls n e1 r).getD p .disabled)
      ((stepForeignRead decls n e2 r).getD p .disabled) = true := by
  intro p
  by_cases hp : p < n
  · rw [stepForeignRead_getD hp, stepForeignRead_getD hp]
    by_cases hm : isMutPtrLocal decls p = true
    · cases hk2 : foreignReadKeeps e2 r p with
      | false =>
        simp only [hm, Bool.not_false, Bool.and_self, ↓reduceIte]
        exact subsumesPtrLocalState_disabled_right _
      | true =>
        cases hk1 : foreignReadKeeps e1 r p with
        | false =>
          rw [foreignReadKeeps_mono hall r p hk2 hk1]
          simp only [hm, Bool.not_false, Bool.not_true, Bool.and_self,
            Bool.and_false, ↓reduceIte, Bool.false_eq_true]
          rfl
        | true =>
          simp only [hm, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact hall p
    · simp only [Bool.not_eq_true] at hm
      simp only [hm, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact hall p
  · rw [stepForeignRead_getD_of_le (Nat.le_of_not_lt hp),
      stepForeignRead_getD_of_le (Nat.le_of_not_lt hp)]
    rfl

theorem stepReborrowRead_mono (decls : List LocalDecl) (n : Nat) {e1 e2 : List PtrLocalState}
    (hall : ∀ p, subsumesPtrLocalState (e1.getD p .disabled) (e2.getD p .disabled) = true)
    (rv : Rvalue) :
    ∀ p, subsumesPtrLocalState ((stepReborrowRead decls n e1 rv).getD p .disabled)
      ((stepReborrowRead decls n e2 rv).getD p .disabled) = true := by
  unfold stepReborrowRead
  cases refReborrowParentOf rv with
  | some r => exact stepForeignRead_mono decls n hall r
  | none => exact hall

/-- `ptrStmtStep` is monotone on width-`decls.length` abstract environments. -/
theorem ptrStmtStep_mono (decls : List LocalDecl) {e1 e2 : List PtrLocalState}
    (hlen1 : e1.length = decls.length) (hlen2 : e2.length = decls.length)
    (hsub : subsumesPtrEnv decls.length e1 e2 = true) (s : MirAst.Statement) :
    subsumesPtrEnv decls.length (ptrStmtStep decls e1 s) (ptrStmtStep decls e2 s) = true := by
  have hall : ∀ p, subsumesPtrLocalState (e1.getD p .disabled) (e2.getD p .disabled) = true :=
    subsumesPtrLocalState_getD_of_length hlen1 hlen2 hsub
  have hsetG : ∀ (E1 E2 : List PtrLocalState),
      (∀ p, subsumesPtrLocalState (E1.getD p .disabled) (E2.getD p .disabled) = true) →
      ∀ i st1 st2, subsumesPtrLocalState st1 st2 = true →
      subsumesPtrEnv decls.length (setPtrLocal decls.length E1 i st1)
        (setPtrLocal decls.length E2 i st2) = true := by
    intro E1 E2 hallE i st1 st2 hst
    simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
    intro q hq
    rw [setPtrLocal, setPtrLocal, getD_map_range _ _ _ hq, getD_map_range _ _ _ hq]
    by_cases hqi : (q == i) = true
    · simp only [hqi, ↓reduceIte]; exact hst
    · simp only [hqi, Bool.false_eq_true, ↓reduceIte]
      exact removePeerFromState_mono i (hallE q)
  have hset := hsetG e1 e2 hall
  have hfr : ∀ r, subsumesPtrEnv decls.length (stepForeignRead decls decls.length e1 r)
      (stepForeignRead decls decls.length e2 r) = true := by
    intro r
    simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
    intro q _
    exact stepForeignRead_mono decls decls.length hall r q
  have hid : subsumesPtrEnv decls.length
      ((List.range decls.length).map (fun q => e1.getD q .disabled))
      ((List.range decls.length).map (fun q => e2.getD q .disabled)) = true := by
    simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
    intro q hq
    rw [getD_map_range _ _ _ hq, getD_map_range _ _ _ hq]
    exact hall q
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign dst rv =>
    obtain ⟨i, projs⟩ := dst
    cases projs with
    | nil =>
      simp only [ptrStmtStep]
      by_cases hi_ptr : isDeclPtrLocal decls i = true
      · simp only [hi_ptr, ↓reduceIte]
        cases directBorrowOf rv with
        | some bp =>
          exact hset i _ _ (subsumesPtrLocalState_refl _)
        | none =>
          cases reborrowParentOf rv with
          | some p =>
            simp only [stepReborrow]
            have hallR := stepReborrowRead_mono decls decls.length hall rv
            apply hsetG _ _ hallR i
            have hp := hallR p
            cases h1 : (stepReborrowRead decls decls.length e1 rv).getD p .disabled with
            | empty => rfl
            | disabled =>
              rw [h1] at hp
              cases h2 : (stepReborrowRead decls decls.length e2 rv).getD p .disabled with
              | empty | live _ _ => rw [h2] at hp; simp [subsumesPtrLocalState] at hp
              | disabled => rfl
            | live t1 ps1 =>
              rw [h1] at hp
              cases h2 : (stepReborrowRead decls decls.length e2 rv).getD p .disabled with
              | empty => rw [h2] at hp; simp [subsumesPtrLocalState] at hp
              | disabled => rfl
              | live t2 ps2 =>
                rw [h2] at hp
                simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
                  List.contains_iff_mem] at hp ⊢
                exact ⟨hp.1, fun r hr => hr⟩
          | none =>
            cases ptrCopySrcOf decls rv with
            | some p =>
              simp only [stepPtrCopy]
              by_cases hip : (i == p) = true
              · simp only [hip, ↓reduceIte]; exact hid
              · simp only [hip, Bool.false_eq_true, ↓reduceIte,
                  subsumesPtrEnv, List.all_eq_true, List.mem_range]
                intro q hq
                rw [getD_map_range _ _ _ hq, getD_map_range _ _ _ hq]
                by_cases hqi : (q == i) = true
                · simp only [hqi, ↓reduceIte]
                  exact addPeerToState_mono i (hall p)
                · simp only [hqi, Bool.false_eq_true, ↓reduceIte]
                  have hr := removePeerFromState_mono i (hall q)
                  cases h1 : removePeerFromState i (e1.getD q .disabled) with
                  | empty => rfl
                  | disabled =>
                    rw [h1] at hr
                    cases h2 : removePeerFromState i (e2.getD q .disabled) with
                    | empty | live _ _ => rw [h2] at hr; simp [subsumesPtrLocalState] at hr
                    | disabled => rfl
                  | live t1 ps1 =>
                    rw [h1] at hr
                    cases h2 : removePeerFromState i (e2.getD q .disabled) with
                    | empty => rw [h2] at hr; simp [subsumesPtrLocalState] at hr
                    | disabled => exact subsumesPtrLocalState_disabled_right _
                    | live t2 ps2 =>
                      rw [h2] at hr
                      have hr0 := hr
                      simp only [subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
                        List.contains_iff_mem] at hr
                      by_cases hc2 : ps2.contains p = true
                      · have hc1 : ps1.contains p = true :=
                          List.contains_iff_mem.mpr (hr.2 p (List.contains_iff_mem.mp hc2))
                        simp only [hc1, hc2, ↓reduceIte]
                        simpa [addPeerToState] using addPeerToState_mono i hr0
                      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
                        by_cases hc1 : ps1.contains p = true
                        · by_cases hci : ps1.contains i = true
                          · simp only [hc1, hci, ↓reduceIte]; exact hr0
                          · simp only [hc1, hci, Bool.false_eq_true, ↓reduceIte,
                              subsumesPtrLocalState, Bool.and_eq_true, List.all_eq_true,
                              List.contains_iff_mem]
                            exact ⟨hr.1, fun r hr2 => List.mem_cons_of_mem i (hr.2 r hr2)⟩
                        · simp only [hc1, Bool.false_eq_true, ↓reduceIte]; exact hr0
            | none => exact hset i _ _ (subsumesPtrLocalState_refl _)
      · simp only [hi_ptr, Bool.false_eq_true, ↓reduceIte]
        cases ptrDerefReadSrc rv with
        | some r => exact hfr r
        | none => exact hid
    | cons hd tl =>
      cases hd with
      | deref =>
        cases tl with
        | nil =>
          simp only [ptrStmtStep]
          cases ptrDerefReadSrc rv with
          | some r => exact stepDerefWrite_mono decls.length (stepForeignRead_mono decls decls.length hall r) i
          | none => exact stepDerefWrite_mono decls.length hall i
        | cons _ _ => exact hid
      | _ => exact hid
  | storageLive i | storageDead i =>
    simp only [ptrStmtStep]
    by_cases hi_ptr : isDeclPtrLocal decls i = true
    · simp only [hi_ptr, ↓reduceIte]; exact hset i _ _ (subsumesPtrLocalState_refl _)
    · simp only [hi_ptr, Bool.false_eq_true, ↓reduceIte]; exact hid
  | deinit p =>
    obtain ⟨i, projs⟩ := p
    cases projs with
    | nil =>
      simp only [ptrStmtStep]
      by_cases hi_ptr : isDeclPtrLocal decls i = true
      · simp only [hi_ptr, ↓reduceIte]; exact hset i _ _ (subsumesPtrLocalState_refl _)
      · simp only [hi_ptr, Bool.false_eq_true, ↓reduceIte]; exact hid
    | cons _ _ => exact hid
  | _ => exact hid

/-- A Tree Borrows read whose read projection cannot overlap the unranged entry
`e`'s target leaves `e` unchanged. -/
theorem updateBorrowPermOnReadAtProj_of_not_overlap {all : List BorrowEntry} {e : BorrowEntry}
    (t : Nat) (r : Option Nat) {proj : List ProjectionElem} (off len : Nat)
    (hrl : e.rangeLen = 0)
    (hov : MirSemantics.projectionsOverlap e.targetProjection proj = false) :
    MirSemantics.updateBorrowPermOnReadAtProj all e t r proj off len = e := by
  have hb : MirSemantics.borrowEntryOverlapsWrite e proj off len = false := by
    simp [MirSemantics.borrowEntryOverlapsWrite, hrl, hov]
  unfold MirSemantics.updateBorrowPermOnReadAtProj
  rw [hb]
  cases Nat.beq e.targetLocal t <;> rfl

/-- Soundness of the abstract transfer `stepForeignRead`: after a Tree Borrows
read through the pointer that `r` holds (tag `rv.tag`, entry `rEntry`), which
updates the borrow table by `freezeTreeBorrowsOnReadAtProj` on `rEntry`'s target
(a dereference read `freezeDerefReadBorrowsAt`, or a reference reborrow's
initial read), `PtrEnvOk` holds for `stepForeignRead … r`: every mutable
pointer/reference local that the read may freeze is `.disabled`, and every other
local keeps its entry (the reader and its tag peers are local to the read,
disjoint targets do not overlap it, and a freeze never disables). -/
theorem PtrEnvOk.foreignRead {body : CapturedMir} {view : List LocalSlot}
    {borrows : List BorrowEntry} {env : List PtrLocalState}
    (hok : PtrEnvOk body view borrows env)
    (hranges : ∀ e ∈ borrows, e.rangeLen = 0)
    {r : Nat} {dr : LocalDecl} (hdr : body.localDecls[r]? = some dr)
    (hr_ptr : isPtrTy dr.ty = true)
    {rv : ProvenancePtr} (hvr : view[r]? = some (.init (.ptr rv 8)))
    {rEntry : BorrowEntry} (hrlk : lookupBorrow borrows rv.tag = some rEntry) :
    PtrEnvOk body view
      (MirSemantics.freezeTreeBorrowsOnReadAtProj borrows borrows rEntry.targetLocal (some rv.tag)
        rEntry.targetProjection rEntry.rangeOffset rEntry.rangeLen)
      (stepForeignRead body.localDecls body.localDecls.length env r) := by
  rw [freezeTreeBorrowsOnReadAtProj_eq_map]
  have hf := updateBorrowPermOnReadAtProj_freezeOrSelf borrows rEntry.targetLocal (some rv.tag)
    rEntry.targetProjection rEntry.rangeOffset rEntry.rangeLen
  generalize hfdef : (fun e => MirSemantics.updateBorrowPermOnReadAtProj borrows e
    rEntry.targetLocal (some rv.tag) rEntry.targetProjection rEntry.rangeOffset
    rEntry.rangeLen) = f at hf ⊢
  have hfapp : ∀ e, f e = MirSemantics.updateBorrowPermOnReadAtProj borrows e
      rEntry.targetLocal (some rv.tag) rEntry.targetProjection rEntry.rangeOffset
      rEntry.rangeLen := fun e => by rw [← hfdef]
  have hr_tag : rEntry.tag = rv.tag := (lookupBorrow_mem_and_tag hrlk).2
  have hfr : f rEntry = rEntry := by
    rw [hfapp]
    exact updateBorrowPermOnReadAtProj_of_descendant _ _ _ _
      (by rw [hr_tag]; exact isBorrowDescendantOrSelf_self _ _)
  have hr_lt : r < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdr).1
  have hr_ok := hok r hr_lt
  intro q hq
  have hq_ok := hok q hq
  rw [stepForeignRead_getD hq]
  split
  · trivial
  · rename_i hkeep
    cases hst : env.getD q .disabled with
    | empty => rw [hst] at hq_ok; exact hq_ok
    | disabled => trivial
    | live qT qP =>
      rw [hst] at hq_ok
      intro dq pvq hdq hqptr hvq
      obtain ⟨⟨eq, hlkq, hndisq, hnfq, htgtq⟩, hpeersq⟩ := hq_ok dq pvq hdq hqptr hvq
      refine ⟨⟨f eq, by rw [hf.lookupBorrow_map, hlkq]; rfl, ?_, ?_, ?_⟩, hpeersq⟩
      · intro hdis
        exact hndisq ((hf.perm_eq_disabled_iff eq).mp hdis)
      · intro hmut
        have hk : foreignReadKeeps env r q = true := by
          revert hkeep
          cases foreignReadKeeps env r q <;> simp [hmut]
        suffices hfe : f eq = eq by rw [hfe]; exact hnfq hmut
        unfold foreignReadKeeps at hk
        rw [hst] at hk
        by_cases hqr : q = r
        · subst hqr
          rw [hvr] at hvq
          simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hvq
          obtain ⟨rfl, _⟩ := hvq
          rw [hrlk] at hlkq
          injection hlkq with h
          subst h
          exact hfr
        · have hqr' : (q == r) = false := beq_false_of_ne hqr
          simp only [hqr', Bool.false_or] at hk
          cases hrst : env.getD r .disabled with
          | empty =>
            rw [hrst] at hr_ok
            exact absurd hvr (hr_ok dr rv hdr hr_ptr)
          | disabled =>
            rw [hrst] at hk
            simp at hk
          | live rT rP =>
            rw [hrst] at hk hr_ok
            obtain ⟨⟨eR, hlkR, _, _, htgtR⟩, hpeersR⟩ := hr_ok dr rv hdr hr_ptr hvr
            rw [hrlk] at hlkR
            injection hlkR with h
            subst h
            simp only [Bool.or_eq_true] at hk
            rcases hk with hpeer | hdisj
            · have htag := hpeersR q (List.contains_iff_mem.mp hpeer) dq pvq hdq hqptr hvq
              rw [htag, hrlk] at hlkq
              injection hlkq with h
              subst h
              exact hfr
            · cases qT with
              | none => simp [targetsDefinitelyDisjoint] at hdisj
              | some qp =>
                cases rT with
                | none => simp [targetsDefinitelyDisjoint] at hdisj
                | some rp =>
                  have h1 := htgtq qp rfl
                  have h2 := htgtR rp rfl
                  obtain ⟨k1, p1⟩ := qp
                  obtain ⟨k2, p2⟩ := rp
                  simp only [Prod.mk.injEq] at h1 h2
                  obtain ⟨hk1, hp1⟩ := h1
                  obtain ⟨hk2, hp2⟩ := h2
                  rw [hfapp]
                  by_cases hloc : eq.targetLocal = rEntry.targetLocal
                  · have hov : borrowProjOverlap p1 p2 = false := by
                      have hk12 : k1 = k2 := by rw [← hk1, ← hk2, hloc]
                      simpa [targetsDefinitelyDisjoint, hk12] using hdisj
                    rw [← hp1, ← hp2] at hov
                    exact updateBorrowPermOnReadAtProj_of_not_overlap _ _ _ _
                      (hranges eq (lookupBorrow_mem_and_tag hlkq).1)
                      (borrowProjOverlap_borrowProjSteps hov)
                  · exact updateBorrowPermOnReadAtProj_of_targetLocal_ne _ _ _ _ hloc
      · intro qq hqq
        rw [hf.targetLocal, hf.targetProjection]
        exact htgtq qq hqq

/-- `PtrEnvOk.foreignRead` for a dereference read `*_r` (`freezeDerefReadBorrowsAt`,
`evalRvalue_derefRead_freeze` with an empty post-dereference projection). -/
theorem PtrEnvOk.derefRead {body : CapturedMir} {view : List LocalSlot}
    {borrows : List BorrowEntry} {env : List PtrLocalState}
    (hok : PtrEnvOk body view borrows env)
    (hranges : ∀ e ∈ borrows, e.rangeLen = 0)
    {r : Nat} {dr : LocalDecl} (hdr : body.localDecls[r]? = some dr)
    (hr_ptr : isPtrTy dr.ty = true)
    {rv : ProvenancePtr} (hvr : view[r]? = some (.init (.ptr rv 8))) :
    PtrEnvOk body view (MirSemantics.freezeDerefReadBorrowsAt view r [] borrows)
      (stepForeignRead body.localDecls body.localDecls.length env r) := by
  unfold MirSemantics.freezeDerefReadBorrowsAt
  simp only [get?, hvr]
  cases hlk : lookupBorrow borrows rv.tag with
  | none =>
    refine PtrEnvOk.of_subsumes ?_ hok
    simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
    intro q hq
    rw [stepForeignRead_getD hq]
    split
    · exact subsumesPtrLocalState_disabled_right _
    · exact subsumesPtrLocalState_refl _
  | some rEntry =>
    simp only [appendProjections_nil_right]
    exact hok.foreignRead hranges hdr hr_ptr hvr hlk

/-- Well-formedness of a `PtrLocalState` at width `n`: peer lists have no
duplicates and contain only local indices `< n`. -/
def PtrStateWf (n : Nat) : PtrLocalState → Prop
  | .empty => True
  | .live _ ps => ps.Nodup ∧ ∀ r ∈ ps, r < n
  | .disabled => True

/-- Strictly decreasing height rank on `PtrLocalState` at width `n`, bounded by
`n + 3` (`Translate.lean`: `ptrEnvAtEntry`). -/
def ptrStateRank (n : Nat) : PtrLocalState → Nat
  | .empty => n + 3
  | .live (some _) ps => ps.length + 2
  | .live none ps => ps.length + 1
  | .disabled => 0

def ptrEnvRank (n : Nat) (env : List PtrLocalState) : Nat :=
  ((List.range n).map (fun q => ptrStateRank n (env.getD q .disabled))).sum

def ptrEntriesRank (b n : Nat) (entries : List (List PtrLocalState)) : Nat :=
  ((List.range b).map (fun dst => ptrEnvRank n (entries.getD dst (initPtrEnv n)))).sum

private theorem nodup_length_le_of_subset {xs ys : List Nat}
    (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x rest ih =>
    obtain ⟨hx_not, hrest_nd⟩ := List.nodup_cons.mp hnd
    have hx_in : x ∈ ys := hsub x (List.mem_cons_self ..)
    have hsub' : ∀ y ∈ rest, y ∈ ys.erase x := by
      intro y hy
      have hy_ne : y ≠ x := fun h => hx_not (h ▸ hy)
      exact (List.mem_erase_of_ne hy_ne).mpr (hsub y (List.mem_cons_of_mem x hy))
    have hlen := ih hrest_nd hsub'
    have herase := List.length_erase_of_mem hx_in
    have hpos : 0 < ys.length := List.length_pos_of_mem hx_in
    simp only [List.length_cons]
    omega

private theorem ptrStateWf_peers_length_le {n : Nat} {t : Option (Nat × List BorrowProjStep)}
    {ps : List Nat} (hwf : PtrStateWf n (.live t ps)) :
    ps.length ≤ n := by
  simpa using nodup_length_le_of_subset hwf.1 (fun r hr => List.mem_range.mpr (hwf.2 r hr))

private theorem filter_eq_or_length_lt {α : Type} (p : α → Bool) (xs : List α) :
    xs.filter p = xs ∨ (xs.filter p).length < xs.length := by
  induction xs with
  | nil => exact .inl rfl
  | cons x rest ih =>
    cases hp : p x with
    | false =>
      right
      simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le p rest)
    | true =>
      simp only [List.filter_cons, hp, ↓reduceIte, List.cons.injEq, true_and, List.length_cons]
      rcases ih with heq | hlt
      · exact .inl heq
      · exact .inr (Nat.succ_lt_succ hlt)

theorem joinPtrLocalState_wf {n : Nat} {s1 s2 : PtrLocalState}
    (h1 : PtrStateWf n s1) (h2 : PtrStateWf n s2) :
    PtrStateWf n (joinPtrLocalState s1 s2) := by
  cases s1 with
  | empty => exact h2
  | disabled => cases s2 <;> trivial
  | live t1 ps1 =>
    cases s2 with
    | empty => exact h1
    | disabled => trivial
    | live t2 ps2 =>
      exact ⟨h1.1.sublist List.filter_sublist,
        fun r hr => h1.2 r (List.mem_filter.mp hr).1⟩

theorem joinPtrLocalState_eq_or_rank_lt {n : Nat} {s1 s2 : PtrLocalState}
    (h2 : PtrStateWf n s2) :
    joinPtrLocalState s1 s2 = s1 ∨
      ptrStateRank n (joinPtrLocalState s1 s2) < ptrStateRank n s1 := by
  cases s1 with
  | empty =>
    cases s2 with
    | empty => exact .inl rfl
    | disabled => right; simp [joinPtrLocalState, ptrStateRank]
    | live t2 ps2 =>
      right
      have hlen := ptrStateWf_peers_length_le h2
      cases t2 <;> simp only [joinPtrLocalState, ptrStateRank] <;> omega
  | disabled =>
    left
    cases s2 <;> rfl
  | live t1 ps1 =>
    cases s2 with
    | empty => exact .inl rfl
    | disabled =>
      right
      cases t1 <;> simp only [joinPtrLocalState, ptrStateRank] <;> omega
    | live t2 ps2 =>
      simp only [joinPtrLocalState]
      have hflt := filter_eq_or_length_lt (fun r => ps2.contains r) ps1
      have hle : (ps1.filter (fun r => ps2.contains r)).length ≤ ps1.length :=
        List.length_filter_le _ ps1
      cases t1 with
      | none =>
        have hif : (if (none == t2) then none else none) =
            (none : Option (Nat × List BorrowProjStep)) := by
          by_cases hb : (none == t2) = true <;> simp [hb]
        rw [hif]
        rcases hflt with heq | hlt
        · left; rw [heq]
        · right; simp only [ptrStateRank]; omega
      | some x =>
        by_cases hbeq : (some x == t2) = true
        · simp only [hbeq, ↓reduceIte]
          rcases hflt with heq | hlt
          · left; rw [heq]
          · right; simp only [ptrStateRank]; omega
        · right
          simp only [hbeq, Bool.false_eq_true, ↓reduceIte, ptrStateRank]
          omega

private theorem ptrStateWf_removePeer {n : Nat} (i : Nat) {s : PtrLocalState}
    (h : PtrStateWf n s) : PtrStateWf n (removePeerFromState i s) := by
  cases s with
  | empty | disabled => trivial
  | live t ps =>
    exact ⟨h.1.sublist List.filter_sublist, fun r hr => h.2 r (List.mem_filter.mp hr).1⟩

private theorem ptrStateWf_addPeer {n i : Nat} (hi : i < n) {s : PtrLocalState}
    (h : PtrStateWf n s) : PtrStateWf n (addPeerToState i s) := by
  cases s with
  | empty | disabled => trivial
  | live t ps =>
    simp only [addPeerToState]
    by_cases hc : ps.contains i = true
    · simp only [hc, ↓reduceIte]; exact h
    · have hni : i ∉ ps := by simpa [List.contains_iff_mem] using hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      refine ⟨List.nodup_cons.mpr ⟨hni, h.1⟩, fun r hr => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hrm
      · exact hi
      · exact h.2 r hrm

private theorem ptrStateWf_singleton {n i : Nat} (hi : i < n)
    (t : Option (Nat × List BorrowProjStep)) :
    PtrStateWf n (.live t [i]) :=
  ⟨List.nodup_cons.mpr ⟨List.not_mem_nil, List.Pairwise.nil⟩,
    fun r hr => by rcases List.mem_cons.mp hr with rfl | hnil; exact hi; cases hnil⟩

private theorem stepDerefWrite_wf {n : Nat} {env : List PtrLocalState}
    (hwf : ∀ p, PtrStateWf n (env.getD p .disabled)) (w p : Nat) (hp : p < n) :
    PtrStateWf n ((stepDerefWrite n env w).getD p .disabled) := by
  unfold stepDerefWrite
  cases hw : env.getD w .disabled with
  | empty => rw [getD_map_range _ _ _ hp]; exact hwf p
  | disabled => rw [getD_map_range _ _ _ hp]; trivial
  | live wT wP =>
    rw [getD_map_range _ _ _ hp]
    have hp_wf := hwf p
    cases hp_eq : env.getD p .disabled with
    | empty => trivial
    | disabled => trivial
    | live qT qP =>
      rw [hp_eq] at hp_wf
      by_cases hc : (wP.contains p || targetsDefinitelyDisjoint qT wT) = true
      · simp only [hc, ↓reduceIte]; exact hp_wf
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]; trivial

theorem stepForeignRead_wf {n : Nat} {decls : List LocalDecl} {env : List PtrLocalState}
    (hwf : ∀ p, PtrStateWf n (env.getD p .disabled)) (r : Nat) :
    ∀ p, PtrStateWf n ((stepForeignRead decls n env r).getD p .disabled) := by
  intro p
  by_cases hp : p < n
  · rw [stepForeignRead_getD hp]
    split
    · simp [PtrStateWf]
    · exact hwf p
  · rw [stepForeignRead_getD_of_le (Nat.le_of_not_lt hp)]
    simp [PtrStateWf]

theorem stepReborrowRead_wf {n : Nat} {decls : List LocalDecl} {env : List PtrLocalState}
    (hwf : ∀ p, PtrStateWf n (env.getD p .disabled)) (rv : Rvalue) :
    ∀ p, PtrStateWf n ((stepReborrowRead decls n env rv).getD p .disabled) := by
  unfold stepReborrowRead
  cases refReborrowParentOf rv with
  | some r => exact stepForeignRead_wf hwf r
  | none => exact hwf

theorem ptrStmtStep_wf (decls : List LocalDecl) (env : List PtrLocalState)
    (hwf : ∀ p, PtrStateWf decls.length (env.getD p .disabled))
    (s : MirAst.Statement) (p : Nat) :
    PtrStateWf decls.length ((ptrStmtStep decls env s).getD p .disabled) := by
  by_cases hp : p < decls.length
  · have hset : ∀ i st, PtrStateWf decls.length st →
        PtrStateWf decls.length ((setPtrLocal decls.length env i st).getD p .disabled) := by
      intro i st hst
      rw [setPtrLocal, getD_map_range _ _ _ hp]
      by_cases hpi : (p == i) = true
      · simp only [hpi, ↓reduceIte]; exact hst
      · simp only [hpi, Bool.false_eq_true, ↓reduceIte]
        exact ptrStateWf_removePeer i (hwf p)
    obtain ⟨kind, span⟩ := s
    cases kind with
    | assign dst rv =>
      obtain ⟨i, projs⟩ := dst
      cases projs with
      | nil =>
        simp only [ptrStmtStep]
        by_cases hi_ptr : isDeclPtrLocal decls i = true
        · simp only [hi_ptr, ↓reduceIte]
          have hi_lt : i < decls.length := by
            unfold isDeclPtrLocal at hi_ptr
            cases hd : decls[i]? with
            | none => simp [hd] at hi_ptr
            | some _ => exact (List.getElem?_eq_some_iff.mp hd).1
          cases directBorrowOf rv with
          | some bp =>
            exact hset i _ (ptrStateWf_singleton hi_lt _)
          | none =>
            cases reborrowParentOf rv with
            | some par =>
              simp only [stepReborrow]
              rw [setPtrLocal, getD_map_range _ _ _ hp]
              by_cases hpi : (p == i) = true
              · simp only [hpi, ↓reduceIte]
                cases (stepReborrowRead decls decls.length env rv).getD par .disabled with
                | empty => trivial
                | disabled => trivial
                | live t _ => exact ptrStateWf_singleton hi_lt t
              · simp only [hpi, Bool.false_eq_true, ↓reduceIte]
                exact ptrStateWf_removePeer i (stepReborrowRead_wf hwf rv p)
            | none =>
              cases ptrCopySrcOf decls rv with
              | some src =>
                simp only [stepPtrCopy]
                by_cases his : (i == src) = true
                · simp only [his, ↓reduceIte, getD_map_range _ _ _ hp]; exact hwf p
                · simp only [his, Bool.false_eq_true, ↓reduceIte, getD_map_range _ _ _ hp]
                  by_cases hpi : (p == i) = true
                  · simp only [hpi, ↓reduceIte]
                    exact ptrStateWf_addPeer hi_lt (hwf src)
                  · simp only [hpi, Bool.false_eq_true, ↓reduceIte]
                    have hr_wf := ptrStateWf_removePeer i (hwf p)
                    cases hr_eq : removePeerFromState i (env.getD p .disabled) with
                    | empty => trivial
                    | disabled => trivial
                    | live t ps =>
                      rw [hr_eq] at hr_wf
                      by_cases hcs : ps.contains src = true
                      · simp only [hcs, ↓reduceIte]
                        change PtrStateWf decls.length (addPeerToState i (.live t ps))
                        exact ptrStateWf_addPeer hi_lt hr_wf
                      · simp only [hcs, Bool.false_eq_true, ↓reduceIte]
                        exact hr_wf
              | none => exact hset i _ trivial
        · simp only [hi_ptr, Bool.false_eq_true, ↓reduceIte]
          cases ptrDerefReadSrc rv with
          | some r => exact stepForeignRead_wf hwf r p
          | none => rw [getD_map_range _ _ _ hp]; exact hwf p
      | cons hd tl =>
        cases hd with
        | deref =>
          cases tl with
          | nil =>
            simp only [ptrStmtStep]
            cases ptrDerefReadSrc rv with
            | some r => exact stepDerefWrite_wf (stepForeignRead_wf hwf r) i p hp
            | none => exact stepDerefWrite_wf hwf i p hp
          | cons _ _ => rw [ptrStmtStep, getD_map_range _ _ _ hp]; exact hwf p
        | _ => rw [ptrStmtStep, getD_map_range _ _ _ hp]; exact hwf p
    | storageLive i | storageDead i =>
      simp only [ptrStmtStep]
      by_cases hi_ptr : isDeclPtrLocal decls i = true
      · simp only [hi_ptr, ↓reduceIte]; exact hset i _ trivial
      · simp only [hi_ptr, Bool.false_eq_true, ↓reduceIte, getD_map_range _ _ _ hp]; exact hwf p
    | deinit pl =>
      obtain ⟨i, projs⟩ := pl
      cases projs with
      | nil =>
        simp only [ptrStmtStep]
        by_cases hi_ptr : isDeclPtrLocal decls i = true
        · simp only [hi_ptr, ↓reduceIte]; exact hset i _ trivial
        · simp only [hi_ptr, Bool.false_eq_true, ↓reduceIte, getD_map_range _ _ _ hp]; exact hwf p
      | cons _ _ => rw [ptrStmtStep, getD_map_range _ _ _ hp]; exact hwf p
    | _ => rw [ptrStmtStep, getD_map_range _ _ _ hp]; exact hwf p
  · have hlen := ptrStmtStep_length decls env s
    have hnone : (ptrStmtStep decls env s)[p]? = none := List.getElem?_eq_none (by omega)
    simp only [List.getD, hnone, Option.getD_none]
    trivial

private def PtrEntriesShape (b n : Nat) (entries : List (List PtrLocalState)) : Prop :=
  entries.length = b ∧
  ∀ dst < b, (entries.getD dst (initPtrEnv n)).length = n ∧
    ∀ p, PtrStateWf n ((entries.getD dst (initPtrEnv n)).getD p .disabled)

private theorem initPtrEntries_shape (b n : Nat) :
    PtrEntriesShape b n (initPtrEntries b n) := by
  refine ⟨by simp [initPtrEntries], fun dst hdst => ?_⟩
  rw [initPtrEntries, getD_map_range _ _ _ hdst]
  refine ⟨by simp [initPtrEnv], fun p => ?_⟩
  by_cases hp : p < n
  · rw [initPtrEnv, getD_map_range _ _ _ hp]; trivial
  · have hnone : (initPtrEnv n)[p]? = none := List.getElem?_eq_none (by simp [initPtrEnv]; omega)
    simp only [List.getD, hnone, Option.getD_none]; trivial

private theorem sum_map_le {α : Type} {xs : List α} {f g : α → Nat}
    (hle : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx := hle x (List.mem_cons_self ..)
    have hr := ih (fun y hy => hle y (List.mem_cons_of_mem x hy))
    omega

private theorem sum_map_le_and_lt_of_ne {α : Type} {xs : List α} {f g : α → Nat}
    (hle : ∀ x ∈ xs, f x ≤ g x)
    {x0 : α} (hx0 : x0 ∈ xs) (hlt : f x0 < g x0) :
    (xs.map f).sum < (xs.map g).sum := by
  induction xs with
  | nil => simp at hx0
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hrest_le : (rest.map f).sum ≤ (rest.map g).sum :=
      sum_map_le (fun z hz => hle z (List.mem_cons_of_mem x hz))
    rcases List.mem_cons.mp hx0 with rfl | hmem
    · omega
    · have hx := hle x (List.mem_cons_self ..)
      have hlt_rest := ih (fun z hz => hle z (List.mem_cons_of_mem x hz)) hmem
      omega

private theorem stepPtrAliasEntries_step (decls : List LocalDecl) (bbs : List BasicBlockData)
    {entries : List (List PtrLocalState)}
    (hsh : PtrEntriesShape bbs.length decls.length entries) :
    PtrEntriesShape bbs.length decls.length (stepPtrAliasEntries decls bbs entries) ∧
    (∀ dst < bbs.length, ∀ q < decls.length,
      ((stepPtrAliasEntries decls bbs entries).getD dst (initPtrEnv decls.length)).getD q .disabled =
        (entries.getD dst (initPtrEnv decls.length)).getD q .disabled ∨
      ptrStateRank decls.length
        (((stepPtrAliasEntries decls bbs entries).getD dst (initPtrEnv decls.length)).getD q .disabled) <
      ptrStateRank decls.length
        ((entries.getD dst (initPtrEnv decls.length)).getD q .disabled)) := by
  let b := bbs.length
  let n := decls.length
  have hfold_wf : ∀ (ss : List MirAst.Statement) (env : List PtrLocalState),
      (∀ p, PtrStateWf n (env.getD p .disabled)) →
      ∀ p, PtrStateWf n ((ss.foldl (ptrStmtStep decls) env).getD p .disabled) := by
    intro ss
    induction ss with
    | nil => intro env hwf p; exact hwf p
    | cons s rest ih =>
      intro env hwf p
      exact ih _ (ptrStmtStep_wf decls env hwf s) p
  have hin_wf : ∀ src, ∀ p, PtrStateWf n ((entries.getD src (initPtrEnv n)).getD p .disabled) := by
    intro src p
    by_cases hs : src < b
    · exact (hsh.2 src hs).2 p
    · have hnone : entries[src]? = none := List.getElem?_eq_none (by rw [hsh.1]; omega)
      have hget_none : entries.getD src (initPtrEnv n) = initPtrEnv n := by
        simp only [List.getD, hnone, Option.getD_none]
      rw [hget_none]
      by_cases hp : p < n
      · rw [initPtrEnv, getD_map_range _ _ _ hp]; trivial
      · have hpnone : (initPtrEnv n)[p]? = none := List.getElem?_eq_none (by simp [initPtrEnv]; omega)
        simp only [List.getD, hpnone, Option.getD_none]; trivial
  have hrow : ∀ dst < b,
      let row' := (stepPtrAliasEntries decls bbs entries).getD dst (initPtrEnv n)
      let row := entries.getD dst (initPtrEnv n)
      row'.length = n ∧
      (∀ p, PtrStateWf n (row'.getD p .disabled)) ∧
      (∀ q < n, row'.getD q .disabled = row.getD q .disabled ∨
        ptrStateRank n (row'.getD q .disabled) < ptrStateRank n (row.getD q .disabled)) := by
    intro dst hdst
    let stepFn (acc : List PtrLocalState) (src : Nat) : List PtrLocalState :=
      match bbs[src]? with
      | some bb =>
        if (termTargets bb.terminator).contains dst then
          joinPtrEnv n acc (bb.statements.foldl (ptrStmtStep decls) (entries.getD src (initPtrEnv n)))
        else acc
      | none => acc
    have hget : (stepPtrAliasEntries decls bbs entries).getD dst (initPtrEnv n) =
        (List.range b).foldl stepFn (entries.getD dst (initPtrEnv n)) := by
      simp only [stepPtrAliasEntries, stepFn, b, n, List.getD, List.getElem?_map,
        List.getElem?_range hdst, Option.map_some, Option.getD_some]
      rfl
    dsimp only []
    rw [hget]
    suffices ∀ (srcs : List Nat) (acc : List PtrLocalState),
        acc.length = n →
        (∀ p, PtrStateWf n (acc.getD p .disabled)) →
        let res := srcs.foldl stepFn acc
        res.length = n ∧
        (∀ p, PtrStateWf n (res.getD p .disabled)) ∧
        (∀ q < n, res.getD q .disabled = acc.getD q .disabled ∨
          ptrStateRank n (res.getD q .disabled) < ptrStateRank n (acc.getD q .disabled)) from
      this (List.range b) (entries.getD dst (initPtrEnv n)) (hsh.2 dst hdst).1 (hsh.2 dst hdst).2
    intro srcs
    induction srcs with
    | nil =>
      intro acc hlen hwf
      exact ⟨hlen, hwf, fun _ _ => .inl rfl⟩
    | cons src rest ih =>
      intro acc hlen hwf
      have h1 : (stepFn acc src).length = n ∧
          (∀ p, PtrStateWf n ((stepFn acc src).getD p .disabled)) ∧
          (∀ q < n, (stepFn acc src).getD q .disabled = acc.getD q .disabled ∨
            ptrStateRank n ((stepFn acc src).getD q .disabled) <
              ptrStateRank n (acc.getD q .disabled)) := by
        dsimp only [stepFn]
        cases bbs[src]? with
        | none => exact ⟨hlen, hwf, fun _ _ => .inl rfl⟩
        | some bb =>
          by_cases hcont : (termTargets bb.terminator).contains dst = true
          · simp only [hcont, ↓reduceIte]
            refine ⟨by simp [joinPtrEnv, n], fun p => ?_, fun q hq => ?_⟩
            · by_cases hp : p < n
              · rw [joinPtrEnv, getD_map_range _ _ _ hp]
                exact joinPtrLocalState_wf (hwf p)
                  (hfold_wf bb.statements _ (hin_wf src) p)
              · let joined := joinPtrEnv n acc
                  (bb.statements.foldl (ptrStmtStep decls) (entries.getD src (initPtrEnv n)))
                have hnone : joined[p]? = none :=
                  List.getElem?_eq_none (by simp [joined, joinPtrEnv, n]; omega)
                change PtrStateWf n (joined[p]?.getD .disabled)
                rw [hnone]
                trivial
            · rw [joinPtrEnv, getD_map_range _ _ _ hq]
              exact joinPtrLocalState_eq_or_rank_lt (hfold_wf bb.statements _ (hin_wf src) q)
          · simp only [hcont, Bool.false_eq_true, ↓reduceIte]
            refine ⟨hlen, hwf, fun _ _ => ?_⟩
            simp
      obtain ⟨hlen2, hwf2, hrk2⟩ := ih (stepFn acc src) h1.1 h1.2.1
      dsimp only [List.foldl_cons]
      refine ⟨hlen2, hwf2, fun q hq => ?_⟩
      rcases h1.2.2 q hq with heq1 | hlt1 <;> rcases hrk2 q hq with heq2 | hlt2
      · left; exact heq2.trans heq1
      · right; rw [← heq1]; exact hlt2
      · right; rw [heq2]; exact hlt1
      · right; exact Nat.lt_trans hlt2 hlt1
  refine ⟨⟨by simp [stepPtrAliasEntries], fun dst hdst => ⟨(hrow dst hdst).1, (hrow dst hdst).2.1⟩⟩,
    fun dst hdst q hq => (hrow dst hdst).2.2 q hq⟩

private theorem sum_replicate_nat (k m : Nat) :
    (List.replicate k m).sum = k * m := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.sum_cons, ih, Nat.add_mul, Nat.one_mul]
    omega

private theorem getElem_eq_getD {α : Type} (xs : List α) (i : Nat) (hi : i < xs.length) (d : α) :
    xs[i] = xs.getD i d := by
  simp [List.getD, List.getElem?_eq_getElem hi]

private theorem ptrEntriesRank_init (b n : Nat) :
    ptrEntriesRank b n (initPtrEntries b n) = b * n * (n + 3) := by
  have henv : ptrEnvRank n (initPtrEnv n) = n * (n + 3) := by
    unfold ptrEnvRank
    have hmap : (List.range n).map (fun q => ptrStateRank n ((initPtrEnv n).getD q .disabled)) =
        List.replicate n (n + 3) := by
      apply List.ext_getElem (by simp)
      intro q hq1 hq2
      have hq : q < n := by simpa using hq1
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      rw [initPtrEnv, getD_map_range _ _ _ hq]
      rfl
    rw [hmap, sum_replicate_nat]
  unfold ptrEntriesRank
  have hmap2 : (List.range b).map
      (fun dst => ptrEnvRank n ((initPtrEntries b n).getD dst (initPtrEnv n))) =
      List.replicate b (n * (n + 3)) := by
    apply List.ext_getElem (by simp)
    intro dst hd1 hd2
    have hdst : dst < b := by simpa using hd1
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    rw [initPtrEntries, getD_map_range _ _ _ hdst, henv]
  rw [hmap2, sum_replicate_nat, Nat.mul_assoc]

/-- Unconditional finite-fuel convergence of `iterPtrAliasEntries` (proving the
`B * n * (n + 3) + 1` height bound stated on `ptrEnvAtEntry` in `Translate.lean`):
on any `decls` and any CFG `bbs`, `iterPtrAliasEntries` reaches an exact fixed
point of `stepPtrAliasEntries decls bbs`. -/
theorem iterPtrAliasEntries_stabilizes (decls : List LocalDecl) (bbs : List BasicBlockData) :
    let n := decls.length
    let b := bbs.length
    let fuel := b * n * (n + 3) + 1
    let init := initPtrEntries b n
    stepPtrAliasEntries decls bbs (iterPtrAliasEntries fuel decls bbs init) =
      iterPtrAliasEntries fuel decls bbs init := by
  dsimp only
  suffices ∀ (fuel : Nat) (entries : List (List PtrLocalState)),
      PtrEntriesShape bbs.length decls.length entries →
      ptrEntriesRank bbs.length decls.length entries < fuel →
      stepPtrAliasEntries decls bbs (iterPtrAliasEntries fuel decls bbs entries) =
        iterPtrAliasEntries fuel decls bbs entries by
    apply this (bbs.length * decls.length * (decls.length + 3) + 1)
      (initPtrEntries bbs.length decls.length) (initPtrEntries_shape bbs.length decls.length)
    rw [ptrEntriesRank_init]
    omega
  intro fuel
  induction fuel with
  | zero => intro _ _ hlt; omega
  | succ k ih =>
    intro entries hsh hlt
    simp only [iterPtrAliasEntries]
    by_cases hbeq : (stepPtrAliasEntries decls bbs entries == entries) = true
    · simp only [hbeq, ↓reduceIte]
      exact beq_iff_eq.mp hbeq
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      have hne : stepPtrAliasEntries decls bbs entries ≠ entries :=
        fun h => hbeq (beq_iff_eq.mpr h)
      obtain ⟨hsh', hstep⟩ := stepPtrAliasEntries_step decls bbs hsh
      have hdiff : ∃ dst < bbs.length, ∃ q < decls.length,
          ((stepPtrAliasEntries decls bbs entries).getD dst (initPtrEnv decls.length)).getD q .disabled ≠
            (entries.getD dst (initPtrEnv decls.length)).getD q .disabled := by
        apply Classical.byContradiction
        intro hall_eq
        apply hne
        apply List.ext_getElem (hsh'.1.trans hsh.1.symm)
        intro dst hd1 hd2
        have hdst : dst < bbs.length := by rw [← hsh'.1]; exact hd1
        rw [getElem_eq_getD _ _ hd1 (initPtrEnv decls.length),
            getElem_eq_getD _ _ hd2 (initPtrEnv decls.length)]
        apply List.ext_getElem ((hsh'.2 dst hdst).1.trans (hsh.2 dst hdst).1.symm)
        intro q hq1 hq2
        have hq : q < decls.length := by rw [← (hsh'.2 dst hdst).1]; exact hq1
        rw [getElem_eq_getD _ _ hq1 .disabled, getElem_eq_getD _ _ hq2 .disabled]
        exact Classical.byContradiction fun hneq => hall_eq ⟨dst, hdst, q, hq, hneq⟩
      obtain ⟨dst0, hdst0, q0, hq0, hneq0⟩ := hdiff
      have hrk_lt : ptrEntriesRank bbs.length decls.length (stepPtrAliasEntries decls bbs entries) <
          ptrEntriesRank bbs.length decls.length entries := by
        unfold ptrEntriesRank
        apply sum_map_le_and_lt_of_ne (x0 := dst0)
        · intro dst hdst_mem
          have hdst : dst < bbs.length := List.mem_range.mp hdst_mem
          unfold ptrEnvRank
          apply sum_map_le
          intro q hq_mem
          have hq : q < decls.length := List.mem_range.mp hq_mem
          rcases hstep dst hdst q hq with heq | hlt_q
          · rw [heq]; exact Nat.le_refl _
          · omega
        · exact List.mem_range.mpr hdst0
        · unfold ptrEnvRank
          apply sum_map_le_and_lt_of_ne (x0 := q0)
          · intro q hq_mem
            have hq : q < decls.length := List.mem_range.mp hq_mem
            rcases hstep dst0 hdst0 q hq with heq | hlt_q
            · rw [heq]; exact Nat.le_refl _
            · omega
          · exact List.mem_range.mpr hq0
          · rcases hstep dst0 hdst0 q0 hq0 with heq | hlt_q
            · exact False.elim (hneq0 heq)
            · exact hlt_q
      exact ih _ hsh' (by omega)

/-- Outgoing CFG edge closure of `ptrEnvAtEntry` holds unconditionally on any
CFG (`iterPtrAliasEntries_stabilizes`). -/
theorem ptrEnvAtEntry_fixed (body : CapturedMir) {src dst : Nat} {bb : BasicBlockData}
    (hbb : body.basicBlocks[src]? = some bb) (hdst : dst < body.basicBlocks.length)
    (htgt : dst ∈ termTargets bb.terminator) :
    subsumesPtrEnv body.localDecls.length
      (bb.statements.foldl (ptrStmtStep body.localDecls) (ptrEnvAtEntry body src))
      (ptrEnvAtEntry body dst) = true := by
  let n := body.localDecls.length
  let b := body.basicBlocks.length
  let fuel := b * n * (n + 3) + 1
  let entries := iterPtrAliasEntries fuel body.localDecls body.basicBlocks (initPtrEntries b n)
  have hfix : stepPtrAliasEntries body.localDecls body.basicBlocks entries = entries :=
    iterPtrAliasEntries_stabilizes body.localDecls body.basicBlocks
  have hsrc : src < b := (List.getElem?_eq_some_iff.mp hbb).1
  change subsumesPtrEnv n
    (bb.statements.foldl (ptrStmtStep body.localDecls) (entries.getD src (initPtrEnv n)))
    (entries.getD dst (initPtrEnv n)) = true
  have hdst_fix : entries.getD dst (initPtrEnv n) =
      (stepPtrAliasEntries body.localDecls body.basicBlocks entries).getD dst (initPtrEnv n) := by
    rw [hfix]
  let stepFn (acc : List PtrLocalState) (s : Nat) : List PtrLocalState :=
    match body.basicBlocks[s]? with
    | some bb' =>
      if (termTargets bb'.terminator).contains dst then
        joinPtrEnv n acc (bb'.statements.foldl (ptrStmtStep body.localDecls) (entries.getD s (initPtrEnv n)))
      else acc
    | none => acc
  have hget : (stepPtrAliasEntries body.localDecls body.basicBlocks entries).getD dst (initPtrEnv n) =
      (List.range b).foldl stepFn (entries.getD dst (initPtrEnv n)) := by
    simp only [stepPtrAliasEntries, stepFn, b, n, List.getD, List.getElem?_map,
      List.getElem?_range hdst, Option.map_some, Option.getD_some]
    rfl
  rw [hdst_fix, hget]
  have hfold_mono : ∀ (srcs : List Nat) (acc : List PtrLocalState),
      subsumesPtrEnv n acc (srcs.foldl stepFn acc) = true := by
    intro srcs
    induction srcs with
    | nil => intro acc; exact subsumesPtrEnv_refl n acc
    | cons s rest ih =>
      intro acc
      have h1 : subsumesPtrEnv n acc (stepFn acc s) = true := by
        dsimp only [stepFn]
        cases body.basicBlocks[s]? with
        | none => exact subsumesPtrEnv_refl n acc
        | some bb' =>
          by_cases hcont : (termTargets bb'.terminator).contains dst = true
          · simp only [hcont, ↓reduceIte]
            exact joinPtrEnv_subsumes_left n acc _
          · simp only [hcont, Bool.false_eq_true, ↓reduceIte]
            exact subsumesPtrEnv_refl n acc
      exact subsumesPtrEnv_trans h1 (ih (stepFn acc s))
  suffices ∀ (srcs : List Nat) (acc : List PtrLocalState),
      src ∈ srcs →
      subsumesPtrEnv n
        (bb.statements.foldl (ptrStmtStep body.localDecls) (entries.getD src (initPtrEnv n)))
        (srcs.foldl stepFn acc) = true from
    this (List.range b) (entries.getD dst (initPtrEnv n)) (List.mem_range.mpr hsrc)
  intro srcs
  induction srcs with
  | nil => intro _ hmem; simp at hmem
  | cons s rest ih =>
    intro acc hmem
    rcases List.mem_cons.mp hmem with rfl | hrest
    · have h1 : subsumesPtrEnv n
          (bb.statements.foldl (ptrStmtStep body.localDecls) (entries.getD src (initPtrEnv n)))
          (stepFn acc src) = true := by
        dsimp only [stepFn]
        rw [hbb]
        simp only [List.contains_iff_mem.mpr htgt, ↓reduceIte]
        exact joinPtrEnv_subsumes_right n acc _
      exact subsumesPtrEnv_trans h1 (hfold_mono rest (stepFn acc src))
    · exact ih (stepFn acc s) hrest

theorem terminatorOk_termTargets_lt {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {nblocks : Nat} {term : MirAst.Terminator}
    (ht : terminatorOk layouts decls nblocks term = true)
    {dst : Nat} (hdst : dst ∈ termTargets term) :
    dst < nblocks := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | goto target =>
    simp only [termTargets, List.mem_singleton] at hdst
    subst hdst
    simpa [terminatorOk] using ht
  | switchInt discr targets =>
    simp only [terminatorOk] at ht
    cases hit : switchIntType layouts decls (copyOp discr) with
    | none => simp [hit] at ht
    | some it =>
      simp only [hit, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
      simp only [termTargets, List.mem_cons, List.mem_map] at hdst
      rcases hdst with rfl | ⟨p, hp, rfl⟩
      · exact ht.2
      · exact (ht.1.1.2 p hp).2
  | call _ _ _ _ _ => simp [terminatorOk] at ht
  | _ => simp [termTargets] at hdst

/-- On any CFG whose terminators satisfy `terminatorOk`, `iterPtrAliasEntries`
stabilizes (`iterPtrAliasEntries_stabilizes`), so `ptrAliasingOk body = true`
holds iff directly-borrowed locals are preserved parameters and every block
satisfies `blockPtrAliasOk` at `ptrEnvAtEntry body blk` (initial-entry and
outgoing-edge subsumption are automatic). -/
theorem ptrAliasingOk_iff_blockPtrAliasOk {body : CapturedMir}
    (hterm : ∀ bb ∈ body.basicBlocks,
      terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true) :
    ptrAliasingOk body = true ↔
      (∀ k ∈ bodyAddrTakenLocals body, 1 ≤ k ∧ k ≤ body.argCount) ∧
      (∀ bb ∈ body.basicBlocks,
        (∀ s ∈ bb.statements, stmtPreservesAddrTaken (bodyAddrTakenLocals body) s = true) ∧
        termPreservesAddrTaken (bodyAddrTakenLocals body) bb.terminator = true) ∧
      (∀ blk (bb : BasicBlockData), body.basicBlocks[blk]? = some bb →
        blockPtrAliasOk body.localDecls (ptrEnvAtEntry body blk) bb.statements = true) := by
  constructor
  · intro hpa
    obtain ⟨hargs, hpres, _, hblks⟩ := ptrAliasingOk_spec hpa
    exact ⟨hargs, hpres, fun blk bb hbb =>
      (hblks blk (List.getElem?_eq_some_iff.mp hbb).1 bb hbb).1⟩
  · rintro ⟨hargs, hpres, hblk⟩
    simp only [ptrAliasingOk, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq]
    refine ⟨⟨⟨hargs, hpres⟩, subsumesPtrEnv_initPtrEnv _ _⟩, fun blk hblk_lt => ?_⟩
    cases hbb : body.basicBlocks[blk]? with
    | none => trivial
    | some bb =>
      simp only [Bool.and_eq_true, List.all_eq_true]
      refine ⟨hblk blk bb hbb, fun dst hdst => ?_⟩
      have hdst_lt : dst < body.basicBlocks.length :=
        terminatorOk_termTargets_lt (hterm bb (List.mem_of_getElem? hbb)) hdst
      exact ptrEnvAtEntry_fixed body hbb hdst_lt hdst

/-- Least fixed-point optimality of `ptrEnvAtEntry`: for any width-`n` pre-fixed
point `entries'` of `body`'s forward pointer-aliasing equations, `ptrEnvAtEntry`
is subsumed by `entries'` at every block `dst < body.basicBlocks.length`. -/
theorem ptrEnvAtEntry_least {body : CapturedMir} {entries' : List (List PtrLocalState)}
    (hlen' : ∀ blk < body.basicBlocks.length,
      (entries'.getD blk (initPtrEnv body.localDecls.length)).length = body.localDecls.length)
    (hpre : ∀ src dst (bb : BasicBlockData),
      body.basicBlocks[src]? = some bb → dst < body.basicBlocks.length →
      dst ∈ termTargets bb.terminator →
      subsumesPtrEnv body.localDecls.length
        (bb.statements.foldl (ptrStmtStep body.localDecls)
          (entries'.getD src (initPtrEnv body.localDecls.length)))
        (entries'.getD dst (initPtrEnv body.localDecls.length)) = true)
    {dst : Nat} (hdst : dst < body.basicBlocks.length) :
    subsumesPtrEnv body.localDecls.length
      (ptrEnvAtEntry body dst)
      (entries'.getD dst (initPtrEnv body.localDecls.length)) = true := by
  let n := body.localDecls.length
  let b := body.basicBlocks.length
  have hfold_ss : ∀ (ss : List MirAst.Statement) {e1 e2 : List PtrLocalState},
      e1.length = n → e2.length = n → subsumesPtrEnv n e1 e2 = true →
      subsumesPtrEnv n
        (ss.foldl (ptrStmtStep body.localDecls) e1)
        (ss.foldl (ptrStmtStep body.localDecls) e2) = true := by
    intro ss
    induction ss with
    | nil => intro _ _ _ _ h; exact h
    | cons s rest ih =>
      intro e1 e2 hl1 hl2 h
      exact ih (ptrStmtStep_length body.localDecls e1 s)
        (ptrStmtStep_length body.localDecls e2 s)
        (ptrStmtStep_mono body.localDecls hl1 hl2 h s)
  suffices ∀ (fuel : Nat) (entries : List (List PtrLocalState)),
      PtrEntriesShape b n entries →
      (∀ blk < b,
        subsumesPtrEnv n (entries.getD blk (initPtrEnv n))
          (entries'.getD blk (initPtrEnv n)) = true) →
      ∀ d < b,
        subsumesPtrEnv n
          ((iterPtrAliasEntries fuel body.localDecls body.basicBlocks entries).getD d (initPtrEnv n))
          (entries'.getD d (initPtrEnv n)) = true from
    this (b * n * (n + 3) + 1) (initPtrEntries b n) (initPtrEntries_shape b n)
      (fun blk hblk => by
        rw [initPtrEntries, getD_map_range _ _ _ hblk]
        exact subsumesPtrEnv_initPtrEnv n _)
      dst hdst
  intro fuel
  induction fuel with
  | zero => intro entries _ hsub d hd; exact hsub d hd
  | succ k ih =>
    intro entries hsh hsub d hd
    simp only [iterPtrAliasEntries]
    split
    · exact hsub d hd
    · apply ih (stepPtrAliasEntries body.localDecls body.basicBlocks entries)
        (stepPtrAliasEntries_step body.localDecls body.basicBlocks hsh).1 _ d hd
      intro blk hblk
      let stepFn (acc : List PtrLocalState) (src : Nat) : List PtrLocalState :=
        match body.basicBlocks[src]? with
        | some bb =>
          if (termTargets bb.terminator).contains blk then
            joinPtrEnv n acc
              (bb.statements.foldl (ptrStmtStep body.localDecls) (entries.getD src (initPtrEnv n)))
          else acc
        | none => acc
      have hget : (stepPtrAliasEntries body.localDecls body.basicBlocks entries).getD blk (initPtrEnv n) =
          (List.range b).foldl stepFn (entries.getD blk (initPtrEnv n)) := by
        simp only [stepPtrAliasEntries, stepFn, b, n, List.getD, List.getElem?_map,
          List.getElem?_range hblk, Option.map_some, Option.getD_some]
        rfl
      rw [hget]
      suffices ∀ (srcs : List Nat) (acc : List PtrLocalState),
          subsumesPtrEnv n acc (entries'.getD blk (initPtrEnv n)) = true →
          subsumesPtrEnv n (srcs.foldl stepFn acc) (entries'.getD blk (initPtrEnv n)) = true from
        this (List.range b) (entries.getD blk (initPtrEnv n)) (hsub blk hblk)
      intro srcs
      induction srcs with
      | nil => intro acc hacc; exact hacc
      | cons src rest ihr =>
        intro acc hacc
        apply ihr (stepFn acc src)
        dsimp only [stepFn]
        cases hbb : body.basicBlocks[src]? with
        | none => exact hacc
        | some bb =>
          by_cases hcont : (termTargets bb.terminator).contains blk = true
          · simp only [hcont, ↓reduceIte]
            have hsrc_lt : src < b := (List.getElem?_eq_some_iff.mp hbb).1
            have htgt : blk ∈ termTargets bb.terminator := List.contains_iff_mem.mp hcont
            have hout_sub := hfold_ss bb.statements (hsh.2 src hsrc_lt).1 (hlen' src hsrc_lt)
              (hsub src hsrc_lt)
            exact joinPtrEnv_least hacc
              (subsumesPtrEnv_trans hout_sub (hpre src blk bb hbb hblk htgt))
          · simp only [hcont, Bool.false_eq_true, ↓reduceIte]
            exact hacc

/-- Mapping from Anneal borrow tags to MiniRust target `(addr, prov)` pairs for
initial-argument target places. -/
def borrowTargets (body : CapturedMir) (ctx : Ctx) (borrows : List BorrowEntry) (tag : Nat) :
    Option (Nat × Option Prov) := do
  let e ← lookupBorrow borrows tag
  let (_, relOff) ← ptrTargetSpec body.layouts body.localDecls ⟨e.targetLocal, e.targetProjection⟩
  let baseAddr := ctx.addrs.getD e.targetLocal 0
  pure ((baseAddr + (relOff : Int)).toNat,
        some (⟨((ctx.base.length + e.targetLocal : Nat) : Int)⟩, ()))

/-- `ctx` enriched with `borrowTargets` for `borrows`. -/
def ctxWithBorrows (body : CapturedMir) (ctx : Ctx) (borrows : List BorrowEntry) : Ctx :=
  { ctx with ptrTargets := borrowTargets body ctx borrows }

@[simp] theorem borrowTargets_nil (body : CapturedMir) (ctx : Ctx) :
    borrowTargets body ctx [] = fun _ => none := by
  funext tag
  rfl

@[simp] theorem ctxWithBorrows_nil (body : CapturedMir) (ctx : Ctx) :
    ctxWithBorrows body ctx [] = { ctx with ptrTargets := fun _ => none } := by
  simp [ctxWithBorrows]

theorem borrowTargets_map_eq (body : CapturedMir) (ctx : Ctx) (borrows : List BorrowEntry)
    (f : BorrowEntry → BorrowEntry)
    (hf : ∀ e, (f e).tag = e.tag ∧ (f e).targetLocal = e.targetLocal ∧
      (f e).targetProjection = e.targetProjection) :
    borrowTargets body ctx (borrows.map f) = borrowTargets body ctx borrows := by
  funext tag
  unfold borrowTargets
  rw [lookupBorrow_map_eq (fun e => (hf e).1) tag]
  cases lookupBorrow borrows tag with
  | none => rfl
  | some e =>
    obtain ⟨_, hloc, hproj⟩ := hf e
    simp [hloc, hproj]

theorem ctxWithBorrows_invalidateDerefWriteBorrows (body : CapturedMir) (ctx : Ctx)
    (locals : List LocalSlot) (borrows : List BorrowEntry)
    (p : Nat) (ptrVal : ProvenancePtr) (entry : BorrowEntry)
    (hp : locals[p]? = some (.init (.ptr ptrVal 8)))
    (he : lookupBorrow borrows ptrVal.tag = some entry)
    (hrlen : entry.rangeLen = 0) (hroff : entry.rangeOffset = 0)
    (hfull : MirSemantics.resolveDerefWriteFullProj locals locals (.ptr ptrVal 8) entry [] =
      entry.targetProjection) :
    ctxWithBorrows body ctx (invalidateDerefWriteBorrows locals borrows ⟨p, [.deref]⟩ []) =
      ctxWithBorrows body ctx borrows := by
  simp only [ctxWithBorrows,
    invalidateDerefWriteBorrows_eq_map locals borrows p ptrVal entry hp he hrlen hroff hfull]
  congr 1
  apply borrowTargets_map_eq
  intro e
  have hf := updateBorrowPermTreeAtProj_fields borrows e entry.targetLocal (some ptrVal.tag)
    entry.targetProjection 0 0
  exact ⟨hf.1, hf.2.1, hf.2.2.1⟩

theorem LocalStorage.extend_ptrTargets {ctx1 ctx2 : Ctx} {A : List Gen.Allocation}
    {d : LocalDecl} {slot : LocalSlot} {p : Ptr} {layouts : Layout.LayoutTable}
    (hbaseEq : ctx1.base = ctx2.base)
    (h : LocalStorage ctx1 A d slot p layouts)
    (hext : isPtrTy d.ty = true → ∀ pv a pr, slot = .init (.ptr pv 8) →
      ctx2.ptrTargets pv.allocId = some (a, pr) → ctx1.ptrTargets pv.allocId = some (a, pr)) :
    LocalStorage ctx2 A d slot p layouts := by
  obtain ⟨id, hpid, hbase, haddr, haddrMax, hcls, hA⟩ := h
  refine ⟨id, hpid, hbaseEq ▸ hbase, haddr, haddrMax, hcls, ?_⟩
  cases hp_ty : isPtrTy d.ty with
  | false =>
    simp only [hp_ty, Bool.false_eq_true, ↓reduceIte] at hA ⊢
    exact hA
  | true =>
    simp only [hp_ty, ↓reduceIte] at hA ⊢
    cases slot with
    | dead => exact hA
    | uninit => exact hA
    | init v =>
      cases v with
      | ptr pv sz =>
        cases Nat.decEq sz 8 with
        | isFalse hne =>
          split at hA
          · next _ heq => injection heq with hv; injection hv with _ hsz; exact absurd hsz hne
          · exact hA
        | isTrue heq =>
          subst heq
          obtain ⟨tAddr, tProv, htlt, htgt, hAk⟩ := hA
          exact ⟨tAddr, tProv, htlt, fun a pr h2 => htgt a pr (hext hp_ty pv a pr rfl h2), hAk⟩
      | _ => exact hA

theorem LocalsOkA.extend_ptrTargets {body : CapturedMir} {ctx1 ctx2 : Ctx} {al : List Nat}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hbaseEq : ctx1.base = ctx2.base)
    (hlo : LocalsOkA body ctx1 al locals lm A)
    (hext : ∀ (i : Nat) d pv a pr, body.localDecls[i]? = some d → isPtrTy d.ty = true →
      locals[i]? = some (.init (.ptr pv 8)) →
      ctx2.ptrTargets pv.allocId = some (a, pr) → ctx1.ptrTargets pv.allocId = some (a, pr)) :
    LocalsOkA body ctx2 al locals lm A :=
  { nlocals := hlo.nlocals
    slots := hlo.slots
    base := hbaseEq ▸ hlo.base
    keysNodup := hlo.keysNodup
    keysLocal := hlo.keysLocal
    live := hlo.live
    storage := fun i d slot p hd hs hp =>
      (hlo.storage i d slot p hd hs hp).extend_ptrTargets hbaseEq
        (fun hp_ty pv a pr hslot h2 => hext i d pv a pr hd hp_ty (hslot ▸ hs) h2)
    inj := hlo.inj
    owned := fun id a ha hlive hb => hlo.owned id a ha hlive (hbaseEq ▸ hb) }

/-- Synchronized borrow-table and flow-sensitive pointer/reference local
invariant for `StateRelN`. -/
structure BorrowsOk (body : CapturedMir) (ctx : Ctx) (view : List LocalSlot)
    (s : MachineState) (lm : Map Gen.LocalName Ptr) : Prop where
  tags_lt : ∀ e ∈ s.memory.borrows, e.tag < s.memory.nextTag
  entries_ok : ∀ e ∈ s.memory.borrows,
    ∃ (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType) (relOff : Nat),
      (e = { rawPtrEntry e.tag mutbl ⟨e.targetLocal, e.targetProjection⟩ with
              parentTag := e.parentTag } ∨
       (mutbl = .mut ∧
         e = { rawPtrEntry e.tag .mut ⟨e.targetLocal, e.targetProjection⟩ with
               perm := .reserved, parentTag := e.parentTag }) ∨
       e = { rawPtrEntry e.tag mutbl ⟨e.targetLocal, e.targetProjection⟩ with
             perm := .disabled, parentTag := e.parentTag }) ∧
      e.targetLocal ∈ bodyAddrTakenLocals body ∧
      ptrTargetSpec body.layouts body.localDecls ⟨e.targetLocal, e.targetProjection⟩ =
        some (pointeeIt, relOff)
  target_ptrs : inFragment body = true → ∀ k ∈ bodyAddrTakenLocals body,
    view[k]? ≠ some .dead ∧
    mapGet lm (localName k) = some (localPtr ctx k) ∧
    (∀ d, body.localDecls[k]? = some d →
      isPtrTy d.ty = false ∧
      AddrOk (ctx.addrs.getD k 0) (itOf d body.layouts) ∧
      ctx.addrs.getD k 0 + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 64)
  alias_ok : PtrEnvOk body view s.memory.borrows
    (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx)
  ptr_slots : ∀ (p : Nat) (dp : LocalDecl) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
      (ptrVal : ProvenancePtr),
    body.localDecls[p]? = some dp →
    ptrPointeeOf dp.ty = some (mutbl, pointeeIt) →
    view[p]? = some (.init (.ptr ptrVal 8)) →
    ∃ (entry : BorrowEntry) (relOff : Nat),
      ptrVal.offsetBytes = 0 ∧
      lookupBorrow s.memory.borrows ptrVal.tag = some entry ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (pointeeIt, relOff)

theorem BorrowsOk.target_ne_of_not_addrTaken {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm) {i : Nat} (hi : i ∉ bodyAddrTakenLocals body) :
    ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i := by
  intro e he heq
  obtain ⟨_, _, _, _, hmem, _⟩ := hb.entries_ok e he
  exact hi (heq ▸ hmem)

/-- Any initialized pointer or reference local `p` whose static `ptrEnvBefore`
entry is not `.disabled` resolves to a live (non-`.disabled`) `BorrowEntry` in
`s.memory.borrows`, and to `.active` or `.reserved` whenever `p` has mutable
pointer/reference type (`mutbl = .mut`). -/
theorem BorrowsOk.usable_of_not_disabled {body : CapturedMir} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm)
    {p : Nat} {dp : LocalDecl} {srcMutbl : MirAst.Mutability} {srcIt : Gen.IntType}
    {ptrVal : ProvenancePtr} {entry : BorrowEntry}
    (hndis_env : (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD p .disabled ≠ .disabled)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : ptrPointeeOf dp.ty = some (srcMutbl, srcIt))
    (hvp : view[p]? = some (.init (.ptr ptrVal 8)))
    (hlk : lookupBorrow s.memory.borrows ptrVal.tag = some entry) :
    entry.perm ≠ .disabled ∧ (srcMutbl = .mut → entry.perm = .active ∨ entry.perm = .reserved) := by
  have hp_lt : p < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdp).1
  have hisPtr : isPtrTy dp.ty = true := by simp [isPtrTy, hp_ty]
  have hp_ok := hb.alias_ok p hp_lt
  cases hst : (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD p .disabled with
  | empty =>
    rw [hst] at hp_ok
    exact False.elim (hp_ok dp ptrVal hdp hisPtr hvp)
  | disabled =>
    exact False.elim (hndis_env hst)
  | live target peers =>
    rw [hst] at hp_ok
    obtain ⟨⟨entry', hlk', hndis', hnf', _⟩, _⟩ := hp_ok dp ptrVal hdp hisPtr hvp
    rw [hlk] at hlk'
    injection hlk' with heq
    subst heq
    refine ⟨hndis', fun hm => ?_⟩
    have hmut : isMutPtrLocal body.localDecls p = true := by
      subst hm
      simp [isMutPtrLocal, hdp, hp_ty]
    have hnf := hnf' hmut
    cases hpe : entry.perm with
    | active => exact .inl rfl
    | reserved => exact .inr rfl
    | frozen => exact absurd hpe hnf
    | disabled => exact absurd hpe hndis'

theorem BorrowsOk.start {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr}
    (hbor : s.memory.borrows = [])
    (htgt : inFragment body = true → ∀ k ∈ bodyAddrTakenLocals body,
      view[k]? ≠ some .dead ∧
      mapGet lm (localName k) = some (localPtr ctx k) ∧
      (∀ d, body.localDecls[k]? = some d →
        isPtrTy d.ty = false ∧
        AddrOk (ctx.addrs.getD k 0) (itOf d body.layouts) ∧
        ctx.addrs.getD k 0 + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 64))
    (hnoPtr : ∀ (p : Nat) dp pv, body.localDecls[p]? = some dp → isPtrTy dp.ty = true →
      view[p]? ≠ some (.init (.ptr pv 8))) :
    BorrowsOk body ctx view s lm where
  tags_lt e he := by simp [hbor] at he
  entries_ok e he := by simp [hbor] at he
  target_ptrs := htgt
  alias_ok p _ := (PtrLocalOk.of_empty (fun dp pv hdp hpty => hnoPtr p dp pv hdp hpty)) _
  ptr_slots p dp mutbl pointeeIt ptrVal hdp hp hv := by
    have hp_ty : isPtrTy dp.ty = true := by simp [isPtrTy, hp]
    exact False.elim (hnoPtr p dp ptrVal hdp hp_ty hv)

theorem BorrowsOk.advance_keep {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {locals' : List LocalSlot} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm)
    {bb : BasicBlockData} {st : MirAst.Statement}
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hstep :
      let env := ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx
      ptrStmtStep body.localDecls env st =
        (List.range body.localDecls.length).map (fun q => env.getD q .disabled)) :
    BorrowsOk body ctx view (advanceStmt s locals' s.memory) lm where
  tags_lt := hb.tags_lt
  entries_ok := hb.entries_ok
  target_ptrs := hb.target_ptrs
  alias_ok := by
    simp only [advanceStmt]
    rw [Nat.add_eq, ptrEnvBefore_succ hbb hst, hstep]
    exact hb.alias_ok.of_map_range
  ptr_slots := hb.ptr_slots

theorem PtrEnvOk.set_nonptr {body : CapturedMir} {view : List LocalSlot}
    {borrows : List BorrowEntry} {env : List PtrLocalState}
    (hok : PtrEnvOk body view borrows env)
    (i : Nat) (slot' : LocalSlot)
    (hnp : ∀ dp pv, body.localDecls[i]? = some dp → isPtrTy dp.ty = true →
      slot' ≠ .init (.ptr pv 8)) :
    PtrEnvOk body (view.set i slot') borrows env := by
  have hv_eq : ∀ (q : Nat) (dq : LocalDecl) (pv : ProvenancePtr),
      body.localDecls[q]? = some dq → isPtrTy dq.ty = true →
      (view.set i slot')[q]? = some (LocalSlot.init (.ptr pv 8)) →
      view[q]? = some (LocalSlot.init (.ptr pv 8)) := by
    intro q dq pv hdq hpty hv
    by_cases hiq : i = q
    · subst hiq
      by_cases hlt : i < view.length
      · rw [List.getElem?_set_self hlt] at hv
        injection hv with hs
        exact False.elim (hnp dq pv hdq hpty hs)
      · rw [List.getElem?_eq_none (by simp; omega)] at hv
        cases hv
    · rwa [List.getElem?_set_ne hiq] at hv
  intro p hp
  have hp_ok := hok p hp
  cases hst : env.getD p .disabled with
  | empty =>
    rw [hst] at hp_ok
    intro dp pv hdp hpty hv
    exact hp_ok dp pv hdp hpty (hv_eq p dp pv hdp hpty hv)
  | disabled => trivial
  | live target peers =>
    rw [hst] at hp_ok
    intro dp pv hdp hpty hv
    obtain ⟨hent, hpeers⟩ := hp_ok dp pv hdp hpty (hv_eq p dp pv hdp hpty hv)
    exact ⟨hent, fun r hr dr pv_r hdr hptr hvr =>
      hpeers r hr dr pv_r hdr hptr (hv_eq r dr pv_r hdr hptr hvr)⟩

theorem BorrowsOk.advance_set_nonptr {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {locals' : List LocalSlot} {lm' : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm')
    {bb : BasicBlockData} {st : MirAst.Statement}
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hstep :
      let env := ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx
      ptrStmtStep body.localDecls env st =
        (List.range body.localDecls.length).map (fun q => env.getD q .disabled))
    (i : Nat) (slot' : LocalSlot)
    (hdead : i ∈ bodyAddrTakenLocals body → slot' ≠ .dead)
    (hnp : ∀ dp pv, body.localDecls[i]? = some dp → isPtrTy dp.ty = true →
      slot' ≠ .init (.ptr pv 8)) :
    BorrowsOk body ctx (view.set i slot') (advanceStmt s locals' s.memory) lm' := by
  have hb' := hb.advance_keep (locals' := locals') hbb hst hstep
  refine {
    tags_lt := hb'.tags_lt
    entries_ok := hb'.entries_ok
    target_ptrs := fun hfrag k hk => by
      obtain ⟨hnd, hlm, hd⟩ := hb'.target_ptrs hfrag k hk
      refine ⟨?_, hlm, hd⟩
      by_cases hik : i = k
      · subst hik
        by_cases hlt : i < view.length
        · rw [List.getElem?_set_self hlt]
          intro h
          injection h with hs
          exact hdead hk hs
        · rw [List.getElem?_eq_none (by simp; omega)]
          simp
      · rw [List.getElem?_set_ne hik]
        exact hnd
    alias_ok := hb'.alias_ok.set_nonptr i slot' hnp
    ptr_slots := ?_ }
  intro p dp mutbl pointeeIt ptrVal hdp hp hv
  by_cases hip : i = p
  · subst hip
    have hp_ty : isPtrTy dp.ty = true := by simp [isPtrTy, hp]
    by_cases hlt : i < view.length
    · rw [List.getElem?_set_self hlt] at hv
      injection hv with hslot
      exact False.elim (hnp dp ptrVal hdp hp_ty hslot)
    · rw [List.getElem?_eq_none (by simp; omega)] at hv
      cases hv
  · rw [List.getElem?_set_ne hip] at hv
    exact hb'.ptr_slots p dp mutbl pointeeIt ptrVal hdp hp hv

theorem BorrowsOk.with_lm {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm lm' : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm)
    (hlm : ∀ k ∈ bodyAddrTakenLocals body, mapGet lm' (localName k) = mapGet lm (localName k)) :
    BorrowsOk body ctx view s lm' :=
  { hb with
    target_ptrs := fun hfrag k hk => by
      obtain ⟨h0, h1, h2⟩ := hb.target_ptrs hfrag k hk
      exact ⟨h0, (hlm k hk).trans h1, h2⟩ }

/-- Anneal's state after jumping to block `t` with slots `locals`. -/
def jumpState (s : MachineState) (t : Nat) (locals : List LocalSlot) : MachineState :=
  { s with frame := { blockIdx := t, stmtIdx := 0, locals := locals } }

/-- Anneal's state after jumping to block `t` with unchanged locals. -/
def gotoState (s : MachineState) (t : Nat) : MachineState :=
  jumpState s t s.frame.locals

theorem BorrowsOk.jump {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm)
    (hpa : ptrAliasingOk body = true)
    {bb : BasicBlockData} (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hstmt : bb.statements.length ≤ s.frame.stmtIdx)
    (target : Nat) (htgt : target ∈ termTargets bb.terminator)
    (locals' : List LocalSlot) :
    BorrowsOk body ctx view (jumpState s target locals') lm :=
  { tags_lt := hb.tags_lt
    entries_ok := hb.entries_ok
    target_ptrs := hb.target_ptrs
    alias_ok :=
      hb.alias_ok.of_subsumes (ptrEnvBefore_jump_subsumes hpa hbb hstmt htgt)
    ptr_slots := hb.ptr_slots }

theorem statementOk_rawPtr_false_of_scalar {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {dst : Place} {mutbl : MirAst.Mutability} {q : Place}
    {span : String}
    (hall : ∀ d ∈ decls, (scalarTypeOf d.ty).isSome = true) :
    statementOk decls ⟨.assign dst (.rawPtr mutbl q), span⟩ layouts = false := by
  rcases dst with ⟨i, projs⟩
  cases projs with
  | nil =>
    simp only [statementOk, copyRv]
    cases hd : decls[i]? with
    | none => rfl
    | some d =>
      have hsc := hall d (List.mem_of_getElem? hd)
      cases hb : isBoolTy d.ty with
      | true => simp [hb, rvalueOkB]
      | false =>
        cases ho : isOrderingTy d.ty with
        | true => simp [hb, ho, rvalueOkO]
        | false =>
          cases htup : intBoolTupleOf d.ty with
          | some it => simp [hb, ho, htup, rvalueOkTuple]
          | none =>
            cases hit : intTypeOf d.ty with
            | some it => simp [hb, ho, htup, hit, rvalueOk, ptrDerefReadOk]
            | none => simp [scalarTypeOf, hb, ho, htup, hit] at hsc
  | cons p1 prest =>
    cases p1 with
    | field idx fieldTy =>
      simp only [statementOk]
      cases (decls[i]? >>= (tupleTypeOf layouts ·.ty)).isSome
      · rfl
      · simp only [Bool.true_and]
        cases placeIntType layouts decls ⟨i, .field idx fieldTy :: prest⟩ with
        | some it => simp [rvalueOk]
        | none =>
          cases tuplePlaceSpec layouts decls ⟨i, .field idx fieldTy :: prest⟩ <;>
            cases placeMirTy decls ⟨i, .field idx fieldTy :: prest⟩ <;>
            simp [tupleRvalueOk]
    | deref =>
      cases prest with
      | nil =>
        simp only [statementOk]
        cases decide (i < decls.length)
        · rfl
        · cases decls[i]? >>= (ptrPointeeOf ·.ty) with
          | none => rfl
          | some pair =>
            obtain ⟨m, pt⟩ := pair
            cases m <;> simp [copyRv, rvalueOk, ptrDerefReadOk]
      | cons _ _ => rfl
    | _ =>
      cases prest with
      | nil =>
        simp only [statementOk]
        cases decls[i]? >>= (arrayTypeOf ·.ty) with
        | none => rfl
        | some pair => simp [rvalueOk]
      | cons _ _ => rfl

theorem statementOk_ref_false_of_scalar {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {dst : Place} {bkind : BorrowKind} {q : Place}
    {span : String}
    (hall : ∀ d ∈ decls, (scalarTypeOf d.ty).isSome = true) :
    statementOk decls ⟨.assign dst (.ref bkind q), span⟩ layouts = false := by
  rcases dst with ⟨i, projs⟩
  cases projs with
  | nil =>
    simp only [statementOk, copyRv]
    cases hd : decls[i]? with
    | none => rfl
    | some d =>
      have hsc := hall d (List.mem_of_getElem? hd)
      cases hb : isBoolTy d.ty with
      | true => simp [hb, rvalueOkB]
      | false =>
        cases ho : isOrderingTy d.ty with
        | true => simp [hb, ho, rvalueOkO]
        | false =>
          cases htup : intBoolTupleOf d.ty with
          | some it => simp [hb, ho, htup, rvalueOkTuple]
          | none =>
            cases hit : intTypeOf d.ty with
            | some it => simp [hb, ho, htup, hit, rvalueOk, ptrDerefReadOk]
            | none => simp [scalarTypeOf, hb, ho, htup, hit] at hsc
  | cons p1 prest =>
    cases p1 with
    | field idx fieldTy =>
      simp only [statementOk]
      cases (decls[i]? >>= (tupleTypeOf layouts ·.ty)).isSome
      · rfl
      · simp only [Bool.true_and]
        cases placeIntType layouts decls ⟨i, .field idx fieldTy :: prest⟩ with
        | some it => simp [rvalueOk]
        | none =>
          cases tuplePlaceSpec layouts decls ⟨i, .field idx fieldTy :: prest⟩ <;>
            cases placeMirTy decls ⟨i, .field idx fieldTy :: prest⟩ <;>
            simp [tupleRvalueOk]
    | deref =>
      cases prest with
      | nil =>
        simp only [statementOk]
        cases decide (i < decls.length)
        · rfl
        · cases decls[i]? >>= (ptrPointeeOf ·.ty) with
          | none => rfl
          | some pair =>
            obtain ⟨m, pt⟩ := pair
            cases m <;> simp [copyRv, rvalueOk, ptrDerefReadOk]
      | cons _ _ => rfl
    | _ =>
      cases prest with
      | nil =>
        simp only [statementOk]
        cases decls[i]? >>= (arrayTypeOf ·.ty) with
        | none => rfl
        | some pair => simp [rvalueOk]
      | cons _ _ => rfl

theorem bodyAddrTakenLocals_nil_of_allScalar {body : CapturedMir}
    (hfrag : inFragment body = true)
    (hall : body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true) :
    ∀ k, k ∉ bodyAddrTakenLocals body := by
  intro k hk
  unfold inFragment at hfrag
  simp only [Bool.and_eq_true, List.all_eq_true] at hfrag
  have hbbs := hfrag.1.1.1.1.1.2
  unfold bodyAddrTakenLocals at hk
  rw [List.mem_flatMap] at hk
  obtain ⟨bb, hbb, hst_mem⟩ := hk
  rw [List.mem_filterMap] at hst_mem
  obtain ⟨st, hst, hkind⟩ := hst_mem
  have hstOk := (hbbs bb hbb).1.2 st hst
  obtain ⟨stKind, span⟩ := st
  cases stKind with
  | assign dst rv =>
    cases rv with
    | rawPtr mutbl q =>
      have hfalse := statementOk_rawPtr_false_of_scalar (layouts := body.layouts)
        (List.all_eq_true.mp hall) (dst := dst) (mutbl := mutbl) (q := q) (span := span)
      rw [hfalse] at hstOk
      cases hstOk
    | ref bkind q =>
      have hfalse := statementOk_ref_false_of_scalar (layouts := body.layouts)
        (List.all_eq_true.mp hall) (dst := dst) (bkind := bkind) (q := q) (span := span)
      rw [hfalse] at hstOk
      cases hstOk
    | _ => simp [directBorrowOf] at hkind
  | _ => simp at hkind

theorem derefPointeeTy_of_ptrPointeeOf {t : MirAst.Ty} {mutbl : MirAst.Mutability}
    {it : Gen.IntType} (h : ptrPointeeOf t = some (mutbl, it)) :
    derefPointeeTy t = some (.Int it) := by
  unfold ptrPointeeOf at h
  cases hk : t.kind with
  | rawPtr m pointee =>
    simp only [hk, Option.map_eq_some_iff] at h
    obtain ⟨⟨s, n⟩, hb, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, rfl⟩ := heq
    simp [derefPointeeTy, translatePointeeRigidTy, translatePointeeRigidTyAux, hk, hb]
  | ref m pointee =>
    simp only [hk, Option.map_eq_some_iff] at h
    obtain ⟨⟨s, n⟩, hb, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, rfl⟩ := heq
    simp [derefPointeeTy, translatePointeeRigidTy, translatePointeeRigidTyAux, hk, hb]
  | _ => simp [hk] at h

theorem evalOperand_copy_deref_uninit (locals : List LocalSlot) (p : Nat)
    (rest : List ProjectionElem)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (layouts : Layout.LayoutTable) (callerLocals : List LocalSlot)
    (ptrVal : ProvenancePtr) (sz : Nat)
    (hp : locals[p]? = some (.init (.ptr ptrVal sz))) (entry : BorrowEntry)
    (he : lookupBorrow borrows ptrVal.tag = some entry) (hperm : entry.perm ≠ .disabled)
    (hu : locals[entry.targetLocal]? = some .uninit) :
    evalOperand locals (.copy ⟨p, .deref :: rest⟩) borrows globals layouts callerLocals = .ub := by
  cases htp : entry.targetProjection with
  | nil =>
    cases hpe : entry.perm with
    | disabled => exact absurd hpe hperm
    | _ => simp [evalOperand, get?, hp, he, hpe, hu] <;> split <;> rfl
  | cons _ _ =>
    cases hpe : entry.perm with
    | disabled => exact absurd hpe hperm
    | _ => simp [evalOperand, get?, hp, he, hpe, hu] <;> split <;> rfl

theorem align_dvd_is_aligned {a b : Nat} {base : Int} {off : Nat}
    (_hapos : 0 < a) (hab : a ∣ b) (haoff : a ∣ off) (hbase : base % (b : Int) = 0) :
    Align.is_aligned ⟨a⟩ (base + (off : Int)) = true := by
  have hab' : (a : Int) ∣ (b : Int) := Int.ofNat_dvd.mpr hab
  have haoff' : (a : Int) ∣ (off : Int) := Int.ofNat_dvd.mpr haoff
  have hbdvd : (a : Int) ∣ base := Int.dvd_trans hab' (Int.dvd_of_emod_eq_zero hbase)
  have hsum : (a : Int) ∣ base + (off : Int) := Int.dvd_add hbdvd haoff'
  simp [Align.is_aligned, Int.emod_eq_zero_of_dvd hsum]

theorem noIndexProj_of_resolveFieldPath {layouts : Layout.LayoutTable}
    {spec leafSpec : TupleSpec} {projs : List ProjectionElem} {roff : Nat}
    (h : resolveFieldPath layouts spec projs = some (roff, leafSpec)) :
    noIndexProj projs = true := by
  induction projs generalizing spec roff leafSpec with
  | nil => rfl
  | cons p tl ih =>
    cases p with
    | field idx fty =>
      cases spec with
      | scalar _ => simp [resolveFieldPath] at h
      | tuple fs sz al =>
        simp only [resolveFieldPath] at h
        cases h1 : fs[idx]? with
        | none => simp [h1] at h
        | some fp =>
          cases h2 : specOfRigidTy layouts fty.kind fty.layoutIdx with
          | none => simp [h1, h2] at h
          | some es =>
            simp only [h1, h2, Option.bind_eq_bind, Option.bind_some] at h
            split at h
            · cases hr : resolveFieldPath layouts fp.2 tl with
              | none => simp [hr] at h
              | some rp => exact ih hr
            · simp at h
    | _ =>
      cases spec <;> simp [resolveFieldPath] at h

theorem ptrTargetSpec_bound {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    (hdeclsOk : ∀ d ∈ decls, localDeclOk layouts d = true)
    {q : Place} {pointeeIt : Gen.IntType} {relOff : Nat}
    (hspec : ptrTargetSpec layouts decls q = some (pointeeIt, relOff)) :
    ∃ d, decls[q.local_]? = some d ∧
      relOff + pointeeIt.size.bytes ≤ tyBytes (tyOf d layouts) := by
  rcases q with ⟨k, projs⟩
  cases projs with
  | nil =>
    simp only [ptrTargetSpec] at hspec
    split at hspec
    · cases hdk : decls[k]? with
      | none => simp [hdk] at hspec
      | some d =>
        simp only [hdk, Option.bind_eq_bind, Option.bind_some, Option.map_eq_some_iff] at hspec
        obtain ⟨it, hit, heq⟩ := hspec
        injection heq with hit_eq hrel0
        cases hit_eq.symm; cases hrel0.symm
        obtain ⟨hTd, _⟩ := tyOf_int (layouts := layouts) hit
        refine ⟨d, rfl, ?_⟩
        rw [hTd]
        simp [tyBytes]
    · simp at hspec
  | cons p1 prest =>
    cases p1 with
    | constantIndex offset minLen fromEnd =>
      cases prest with
      | nil =>
        simp only [ptrTargetSpec] at hspec
        split at hspec
        · cases hdk : decls[k]? with
          | none => simp [hdk] at hspec
          | some d =>
            simp only [hdk, Option.bind_eq_bind, Option.bind_some] at hspec
            cases ha : arrayTypeOf d.ty with
            | none => simp [ha] at hspec
            | some apair =>
              obtain ⟨elemIt, count⟩ := apair
              simp only [ha] at hspec
              by_cases hc_bounds : minLen ≤ count ∧
                  (if fromEnd then 1 ≤ offset ∧ offset ≤ count else offset < count)
              · simp [hc_bounds] at hspec
                obtain ⟨he1, he2⟩ := hspec
                subst elemIt; subst relOff
                obtain ⟨hTd, _⟩ := tyOf_array (layouts := layouts) ha
                refine ⟨d, rfl, ?_⟩
                rw [hTd]
                simp only [tyBytes]
                have hc_eq : (Int.ofNat count).toNat = count := rfl
                rw [hc_eq]
                let idx := if fromEnd then count - offset else offset
                have hidx_lt : idx < count := by
                  dsimp only [idx]
                  cases fromEnd <;> simp_all <;> omega
                have hle : (idx + 1) * pointeeIt.size.bytes ≤ count * pointeeIt.size.bytes :=
                  Nat.mul_le_mul_right pointeeIt.size.bytes hidx_lt
                rw [Nat.add_mul, Nat.one_mul] at hle
                exact hle
              · simp [hc_bounds] at hspec
        · simp at hspec
      | cons _ _ => simp [ptrTargetSpec] at hspec
    | field idx fieldTy =>
      simp only [ptrTargetSpec] at hspec
      split at hspec
      · cases hdk : decls[k]? with
        | none => simp [hdk] at hspec
        | some d =>
          simp only [hdk, Option.bind_eq_bind, Option.bind_some] at hspec
          cases ht : tupleTypeOf layouts d.ty with
          | none => simp [ht] at hspec
          | some tpair =>
            obtain ⟨fields, size, align⟩ := tpair
            simp only [ht, Option.bind_some] at hspec
            cases hres : resolveFieldPath layouts (.tuple fields size align)
                (.field idx fieldTy :: prest) with
            | none => simp [hres] at hspec
            | some rpair =>
              obtain ⟨relOff', leafSpec⟩ := rpair
              cases leafSpec with
              | tuple _ _ _ => simp [hres] at hspec
              | scalar leafIt =>
                simp only [hres, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hspec
                obtain ⟨he1, he2⟩ := hspec
                cases he1.symm; cases he2.symm
                obtain ⟨hTd, _⟩ := tyOf_tupleSpec ht
                have hwf : (TupleSpec.tuple fields size align).wf = true := by
                  simpa [localDeclOk, scalarTypeOf_none_of_tupleTypeOf ht,
                    arrayTypeOf_none_of_tupleTypeOf ht, ht, isPtrTy_false_of_tupleTypeOf ht] using
                    hdeclsOk d (List.mem_of_getElem? hdk)
                obtain ⟨_, hrelBound⟩ := resolveFieldPath_wf hwf hres
                refine ⟨d, rfl, ?_⟩
                rw [hTd]
                simpa [TupleSpec.toMiniRustTy, tyBytes, TupleSpec.size] using hrelBound
      · simp at hspec
    | _ => simp [ptrTargetSpec] at hspec

theorem evalTargetPlace_deref {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm)
    (hfrag : inFragment body = true)
    (q : Place) (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff))
    (hk_addr : q.local_ ∈ bodyAddrTakenLocals body) :
    0 < (ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat ∧
    CM.dereferenceable m.mem (offsetPtr (localPtr ctx q.local_) relOff) pointeeIt.size = .ok () := by
  obtain ⟨d, hdk, hbound⟩ := ptrTargetSpec_bound h.declsOk hspec
  obtain ⟨_, hlm_k, hd_k⟩ := hb.target_ptrs hfrag q.local_ hk_addr
  obtain ⟨_, haddrOk, _⟩ := hd_k d hdk
  have hpos : 0 < ctx.addrs.getD q.local_ 0 := haddrOk.2.1
  have hk_lt : q.local_ < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdk).1
  obtain ⟨_, slotk, hdk', hsk⟩ := h.slot_exists q.local_ hk_lt
  rw [hdk] at hdk'; cases hdk'
  obtain ⟨allocId, data, hpk, _, _, _, _, hlen, hAk⟩ :=
    h.locs.storage_any hdk hsk hlm_k (h.declsOk d (List.mem_of_getElem? hdk))
  refine ⟨by omega, ?_⟩
  exact cm_dereferenceable_offsetPtr h.shape (localPtr ctx q.local_) allocId hpk
    (itOf d body.layouts) data hAk relOff pointeeIt.size (by omega)

theorem evalTargetPlace {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm)
    (hns : NonScalarLive body view lm)
    (hfrag : inFragment body = true)
    (q : Place) (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff))
    (hk_addr : q.local_ ∈ bodyAddrTakenLocals body) :
    noIndexProj q.projection = true ∧
    (∀ rest, q.projection ≠ .deref :: rest) ∧
    GoodSize pointeeIt.size.bytes ∧
    (ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat < 2 ^ 64 ∧
    ({ addr := ((ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat : Int),
       provenance := some (⟨((ctx.base.length + q.local_ : Nat) : Int)⟩, ()) } : Ptr) =
      offsetPtr (localPtr ctx q.local_) relOff ∧
    Align.is_aligned ⟨pointeeIt.size.bytes⟩ (offsetPtr (localPtr ctx q.local_) relOff).addr = true ∧
    (∀ targetPe, translatePlace body.localDecls q = some targetPe →
      evalPlace m targetPe =
        .ok (({ ptr := { thin_pointer := offsetPtr (localPtr ctx q.local_) relOff, metadata := none },
                 aligned := true }, .Int pointeeIt), m)) := by
  obtain ⟨hnd_k, hlm_k, hd_k⟩ := hb.target_ptrs hfrag q.local_ hk_addr
  rcases q with ⟨k, projs⟩
  simp only [] at hk_addr hnd_k hlm_k hd_k ⊢
  cases projs with
  | nil =>
    simp only [ptrTargetSpec] at hspec
    split at hspec
    · next hrange =>
      cases hdk : body.localDecls[k]? with
      | none => simp [hdk] at hspec
      | some d =>
        simp only [hdk, Option.bind_eq_bind, Option.bind_some, Option.map_eq_some_iff] at hspec
        obtain ⟨it, hit, heq⟩ := hspec
        injection heq with hit_eq hrel0
        cases hit_eq.symm; cases hrel0.symm
        have hgood := intTypeOf_good hit
        have hpos := hgood.pos
        obtain ⟨hnotPtr, haddrOk, haddrMax⟩ := hd_k d hdk
        obtain ⟨hTd, hitd⟩ := tyOf_int (layouts := body.layouts) hit
        rw [hitd] at haddrOk
        rw [hTd] at haddrMax
        simp only [tyBytes] at haddrMax
        have hbase0 : 0 ≤ ctx.addrs.getD k 0 := haddrOk.nonneg
        have htlt : (ctx.addrs.getD k 0 + (0 : Int)).toNat < 2 ^ 64 := by
          have : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := by decide
          omega
        have hptrEq :
            ({ addr := ((ctx.addrs.getD k 0 + (0 : Int)).toNat : Int),
               provenance := some (⟨((ctx.base.length + k : Nat) : Int)⟩, ()) } : Ptr) =
            offsetPtr (localPtr ctx k) 0 := by
          simp only [offsetPtr, localPtr]
          rw [Int.toNat_of_nonneg (by omega)]
          rfl
        have hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (offsetPtr (localPtr ctx k) 0).addr = true := by
          simpa [offsetPtr, localPtr] using
            align_dvd_is_aligned hpos (Nat.dvd_refl _) (Nat.dvd_zero _) haddrOk.1
        refine ⟨rfl, by simp, hgood, htlt, hptrEq, hal, fun targetPe hpe => ?_⟩
        simp only [translatePlace, Option.some.injEq] at hpe
        subst hpe
        have hloc := (h.hf.2 k d hdk).2
        rw [hTd] at hloc
        have hev := evalPlace_local_some h.shape k (.Int pointeeIt) hloc (localPtr ctx k) hlm_k
        simpa [offsetPtr] using hev
    · simp at hspec
  | cons p1 prest =>
    cases p1 with
    | constantIndex offset minLen fromEnd =>
      cases prest with
      | nil =>
        simp only [ptrTargetSpec] at hspec
        split at hspec
        · next hrange =>
          cases hdk : body.localDecls[k]? with
          | none => simp [hdk] at hspec
          | some d =>
            simp only [hdk, Option.bind_eq_bind, Option.bind_some] at hspec
            cases ha : arrayTypeOf d.ty with
            | none => simp [ha] at hspec
            | some apair =>
              obtain ⟨elemIt, count⟩ := apair
              simp only [ha] at hspec
              by_cases hc_bounds : minLen ≤ count ∧
                  (if fromEnd then 1 ≤ offset ∧ offset ≤ count else offset < count)
              · simp [hc_bounds] at hspec
                obtain ⟨he1, he2⟩ := hspec
                subst elemIt; subst relOff
                have hgood := arrayTypeOf_good ha
                have hpos := hgood.pos
                obtain ⟨hnotPtr, haddrOk, haddrMax⟩ := hd_k d hdk
                obtain ⟨hTd, hitd⟩ := tyOf_array (layouts := body.layouts) ha
                rw [hitd] at haddrOk
                rw [hTd] at haddrMax
                simp only [tyBytes] at haddrMax
                have hc_eq : (Int.ofNat count).toNat = count := rfl
                rw [hc_eq] at haddrMax
                have hbase0 : 0 ≤ ctx.addrs.getD k 0 := haddrOk.nonneg
                let idx := if fromEnd then count - offset else offset
                have hidx_lt : idx < count := by
                  dsimp only [idx]
                  cases fromEnd <;> simp_all <;> omega
                have hoff_lt : idx * pointeeIt.size.bytes < count * pointeeIt.size.bytes :=
                  Nat.mul_lt_mul_of_pos_right hidx_lt hpos
                have hoff_int : ((idx * pointeeIt.size.bytes : Nat) : Int) <
                    (count : Int) * (pointeeIt.size.bytes : Int) := by
                  rw [← Int.natCast_mul]
                  exact Int.ofNat_lt.mpr hoff_lt
                have htlt : (ctx.addrs.getD k 0 + ((idx * pointeeIt.size.bytes : Nat) : Int)).toNat < 2 ^ 64 := by
                  have : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := by decide
                  omega
                have hptrEq :
                    ({ addr := ((ctx.addrs.getD k 0 + ((idx * pointeeIt.size.bytes : Nat) : Int)).toNat : Int),
                       provenance := some (⟨((ctx.base.length + k : Nat) : Int)⟩, ()) } : Ptr) =
                    offsetPtr (localPtr ctx k) (idx * pointeeIt.size.bytes) := by
                  simp only [offsetPtr, localPtr]
                  rw [Int.toNat_of_nonneg (by omega)]
                have hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩
                    (offsetPtr (localPtr ctx k) (idx * pointeeIt.size.bytes)).addr = true := by
                  have hdvd : pointeeIt.size.bytes ∣ idx * pointeeIt.size.bytes :=
                    ⟨idx, Nat.mul_comm _ _⟩
                  simpa [offsetPtr, localPtr] using
                    align_dvd_is_aligned hpos (Nat.dvd_refl _) hdvd haddrOk.1
                refine ⟨rfl, by simp, hgood, htlt, hptrEq, hal, fun targetPe hpe => ?_⟩
                have hbound := h.array_bound k d pointeeIt count hdk ha
                have hcnt_lt : count < 2 ^ 63 := by
                  have h1 : count * 1 ≤ count * pointeeIt.size.bytes :=
                    Nat.mul_le_mul_left count hpos
                  omega
                have hoff_263 : offset < 2 ^ 63 := by
                  cases fromEnd <;> simp_all <;> omega
                have hprojOk : projOk body.localDecls count (.constantIndex offset minLen fromEnd) = true := by
                  cases fromEnd <;> simp_all [projOk]
                have hprojIdx : projIdx view count (.constantIndex offset minLen fromEnd) = some idx := by
                  have hnot_lt : ¬ (count < minLen) := by omega
                  simp [projIdx, hnot_lt, idx, hidx_lt]
                exact evalPlace_constantIndex_same h k d hdk pointeeIt count ha (localPtr ctx k) hlm_k
                  offset minLen fromEnd hprojOk targetPe hpe idx hprojIdx
              · simp [hc_bounds] at hspec
        · simp at hspec
      | cons _ _ => simp [ptrTargetSpec] at hspec
    | field idx fieldTy =>
      simp only [ptrTargetSpec] at hspec
      split at hspec
      · next hrange =>
        cases hdk : body.localDecls[k]? with
        | none => simp [hdk] at hspec
        | some d =>
          simp only [hdk, Option.bind_eq_bind, Option.bind_some] at hspec
          cases ht : tupleTypeOf body.layouts d.ty with
          | none => simp [ht] at hspec
          | some tpair =>
            obtain ⟨fields, size, align⟩ := tpair
            simp only [ht, Option.bind_some] at hspec
            cases hres : resolveFieldPath body.layouts (.tuple fields size align)
                (.field idx fieldTy :: prest) with
            | none => simp [hres] at hspec
            | some rpair =>
              obtain ⟨relOff', leafSpec⟩ := rpair
              cases leafSpec with
              | tuple _ _ _ => simp [hres] at hspec
              | scalar leafIt =>
                simp only [hres, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hspec
                obtain ⟨he1, he2⟩ := hspec
                cases he1.symm; cases he2.symm
                obtain ⟨hnotPtr, haddrOk, haddrMax⟩ := hd_k d hdk
                obtain ⟨hTd, hitd⟩ := tyOf_tupleSpec ht
                rw [hitd] at haddrOk
                rw [hTd] at haddrMax
                simp only [TupleSpec.toMiniRustTy, tyBytes] at haddrMax
                obtain ⟨_, slotk, hdk', hsk⟩ := h.slot_exists k hrange.2
                rw [hdk] at hdk'; cases hdk'
                obtain ⟨rootVal, rfl⟩ :=
                  (hns k d slotk hdk hsk (scalarTypeOf_none_of_tupleTypeOf ht) hnotPtr).1
                have hslotOk := (DeclSlotOk_of_tupleTypeOf ht (.init rootVal)).mp
                  (h.slots k d (.init rootVal) hdk hsk)
                have hrootWf := hslotOk.1
                obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hrootWf hres
                have hgood : GoodSize pointeeIt.size.bytes :=
                  (goodAlignBytes_iff pointeeIt.size.bytes).mp hleafWf
                have hpos := hgood.pos
                have hrel_lt : relOff < size := by simp [TupleSpec.size] at hrelBound; omega
                have hbase0 : 0 ≤ ctx.addrs.getD k 0 := haddrOk.nonneg
                have htlt : (ctx.addrs.getD k 0 + (relOff : Int)).toNat < 2 ^ 64 := by
                  have : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := by decide
                  omega
                have hptrEq :
                    ({ addr := ((ctx.addrs.getD k 0 + (relOff : Int)).toNat : Int),
                       provenance := some (⟨((ctx.base.length + k : Nat) : Int)⟩, ()) } : Ptr) =
                    offsetPtr (localPtr ctx k) relOff := by
                  simp only [offsetPtr, localPtr]
                  rw [Int.toNat_of_nonneg (by omega)]
                obtain ⟨halignDvd, hoffDvd⟩ := resolveFieldPath_align hrootWf hres
                have hal : Align.is_aligned ⟨pointeeIt.size.bytes⟩
                    (offsetPtr (localPtr ctx k) relOff).addr = true := by
                  simpa [offsetPtr, localPtr] using
                    align_dvd_is_aligned hpos halignDvd hoffDvd haddrOk.1
                have hnoIdx : noIndexProj (.field idx fieldTy :: prest) = true :=
                  noIndexProj_of_resolveFieldPath hres
                refine ⟨hnoIdx, by simp, hgood, htlt, hptrEq, hal, fun targetPe hpe => ?_⟩
                have hloc := (h.hf.2 k d hdk).2
                rw [hTd] at hloc
                obtain ⟨allocId, hpk, _, _, _, _, hAk⟩ :=
                  h.locs.storage_nonptr k d (.init rootVal) (localPtr ctx k) hdk hsk hlm_k hnotPtr
                rw [declSlotData_of_tupleSpec ht] at hAk
                have hdlen : ((TupleSpec.tuple fields size align).encodeVal rootVal).length = size :=
                  TupleSpec.encodeVal_length (.tuple fields size align) rootVal hrootWf
                have hbound : size < 2 ^ 63 := by
                  simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hrootWf
                  exact hrootWf.1.2
                have hrootEval : evalPlace m (.Local (localName k)) =
                    .ok (({ ptr := { thin_pointer := offsetPtr (localPtr ctx k) 0, metadata := none },
                             aligned := true },
                           (TupleSpec.tuple fields size align).toMiniRustTy), m) := by
                  simpa [offsetPtr] using evalPlace_local_some h.shape k _ hloc (localPtr ctx k) hlm_k
                have hpeEval := evalPlace_ptr_fieldPath h.shape (localPtr ctx k) allocId hpk
                  (itOf d body.layouts) ((TupleSpec.tuple fields size align).encodeVal rootVal) hAk
                  (by rw [hdlen]; exact hbound) hbase0 (by rw [hdlen]; exact haddrMax)
                  (.Local (localName k)) 0 (.tuple fields size align) hrootEval hrootWf
                  (by simp [TupleSpec.size, hdlen]) (.field idx fieldTy :: prest) targetPe hpe
                  relOff (.scalar pointeeIt) hres
                simpa [TupleSpec.toMiniRustTy] using hpeEval
      · simp at hspec
    | _ => simp [ptrTargetSpec] at hspec

theorem evalPtrLoad {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm)
    (hns : NonScalarLive body view lm)
    (hfrag : inFragment body = true)
    (p : Nat) (dp : LocalDecl) (srcMutbl : MirAst.Mutability) (srcIt : Gen.IntType)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : ptrPointeeOf dp.ty = some (srcMutbl, srcIt)) :
    (∃ (ptrVal : ProvenancePtr) (entry : BorrowEntry) (relOff : Nat) (m1 : Mach),
      view[p]? = some (.init (.ptr ptrVal 8)) ∧
      ptrVal.offsetBytes = 0 ∧
      lookupBorrow s.memory.borrows ptrVal.tag = some entry ∧
      entry.targetLocal ∈ bodyAddrTakenLocals body ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) ∧
      evalValue m (.Load (.Local (localName p))) =
        .ok ((.Ptr { thin_pointer := offsetPtr (localPtr ctx entry.targetLocal) relOff, metadata := none },
              declPtrTy dp.ty), m1) ∧
      FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m1 blk stmt) ∨
    ((view[p]? = some .uninit ∨ view[p]? = some .dead) ∧
      ∃ msg, evalValue m (.Load (.Local (localName p))) = .error (.ub msg)) := by
  have hp_lt : p < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdp).1
  have hisPtr : isPtrTy dp.ty = true := by simp [isPtrTy, hp_ty]
  obtain ⟨hTdp, hitdp⟩ := tyOf_isPtrTy (layouts := body.layouts) hisPtr
  have hloc := (h.hf.2 p dp hdp).2
  rw [hTdp] at hloc
  obtain ⟨_, slotp, hdp', hsp⟩ := h.slot_exists p hp_lt
  rw [hdp] at hdp'; cases hdp'
  have hslotOk := h.slots p dp slotp hdp hsp
  cases slotp with
  | dead =>
    right
    refine ⟨.inr hsp, ?_⟩
    cases hlm_p : mapGet lm (localName p) with
    | none =>
      exact ⟨"access to a dead local",
        by simp [evalValue, evalPlace_local_none h.shape p (declPtrTy dp.ty) hloc hlm_p]⟩
    | some ptr_p =>
      obtain ⟨id, hpid, _, _, _, _, hAp⟩ := h.locs.storage p dp .dead ptr_p hdp hsp hlm_p
      simp only [hisPtr, ↓reduceIte, declSlotData_of_isPtrTy hisPtr, hitdp] at hAp
      obtain ⟨msg, hmsg⟩ := typedLoad_ptr_declPtrTy_uninit h.shape ptr_p id hpid dp.ty hAp
      exact ⟨msg, by simp [evalValue, evalPlace_local_some h.shape p (declPtrTy dp.ty) hloc ptr_p hlm_p,
        placeLoad, hmsg]⟩
  | uninit =>
    right
    refine ⟨.inl hsp, ?_⟩
    obtain ⟨ptr_p, hlm_p⟩ := h.locs.some_of_live hsp (by simp)
    obtain ⟨id, hpid, _, _, _, _, hAp⟩ := h.locs.storage p dp .uninit ptr_p hdp hsp hlm_p
    simp only [hisPtr, ↓reduceIte, declSlotData_of_isPtrTy hisPtr, hitdp] at hAp
    obtain ⟨msg, hmsg⟩ := typedLoad_ptr_declPtrTy_uninit h.shape ptr_p id hpid dp.ty hAp
    exact ⟨msg, by simp [evalValue, evalPlace_local_some h.shape p (declPtrTy dp.ty) hloc ptr_p hlm_p,
      placeLoad, hmsg]⟩
  | init v =>
    left
    obtain ⟨ptrVal, rfl⟩ := (DeclSlotOk_of_isPtrTy hisPtr (.init v)).mp hslotOk
    obtain ⟨entry, relOff, hoff0, hlookup, htspec⟩ :=
      hb.ptr_slots p dp srcMutbl srcIt ptrVal hdp hp_ty hsp
    obtain ⟨hentry_mem, _⟩ := lookupBorrow_mem_and_tag hlookup
    obtain ⟨_, _, _, _, hk_addr, _⟩ := hb.entries_ok entry hentry_mem
    obtain ⟨_, _, hgood, htlt, hptrEq, hal, _⟩ :=
      evalTargetPlace h hb hns hfrag ⟨entry.targetLocal, entry.targetProjection⟩ srcIt relOff htspec hk_addr
    obtain ⟨htpos, htderef⟩ :=
      evalTargetPlace_deref h hb hfrag ⟨entry.targetLocal, entry.targetProjection⟩ srcIt relOff htspec hk_addr
    obtain ⟨ptr_p, hlm_p⟩ := h.locs.some_of_live hsp (by simp)
    obtain ⟨id, hpid, _, _, _, _, hAp⟩ :=
      h.locs.storage p dp (.init (.ptr ptrVal 8)) ptr_p hdp hsp hlm_p
    simp only [hisPtr, ↓reduceIte, hitdp] at hAp
    obtain ⟨tAddr, tProv, htlt0, htgt, hAk⟩ := hAp
    have hbt : (ctxWithBorrows body ctx s.memory.borrows).ptrTargets ptrVal.allocId =
        some ((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat,
              some (⟨((ctx.base.length + entry.targetLocal : Nat) : Int)⟩, ())) := by
      simp [ctxWithBorrows, borrowTargets, ProvenancePtr.tag] at hlookup ⊢
      simp [hlookup, htspec]
    obtain ⟨rfl, rfl⟩ := htgt _ _ hbt
    have htal : Align.is_aligned ⟨srcIt.size.bytes⟩
        (((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat : Int)) = true := by
      rw [← hptrEq] at hal
      exact hal
    have htderef' : CM.dereferenceable m.mem
        { addr := ((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat : Int),
          provenance := some (⟨((ctx.base.length + entry.targetLocal : Nat) : Int)⟩, ()) }
        srcIt.size = .ok () := by
      rw [← hptrEq] at htderef
      exact htderef
    obtain ⟨m1, hm1, hs1⟩ := typedLoad_ptr_declPtrTy h.shape ptr_p id hpid dp.ty srcMutbl srcIt
      hp_ty hgood _ htpos htlt0 _ htal htderef' hAk
    rw [hptrEq] at hm1
    refine ⟨ptrVal, entry, relOff, m1, hsp, hoff0, hlookup, hk_addr, htspec,
      by simp [evalValue, evalPlace_local_some h.shape p (declPtrTy dp.ty) hloc ptr_p hlm_p,
        placeLoad, hm1],
      FrameOk.mk' h.hf hs1 h.locs h.declsOk h.nonScalar⟩

/-! ## Symbolic Tree Borrows state-machine & protector invariants (`spec/mem/tree_borrows/*`) -/

/-- Unprotected foreign writes always succeed without UB
(`spec/mem/tree_borrows/state_machine_unprotected.md`). -/
theorem PermissionUnprot.foreign_write_ok (p : Gen.PermissionUnprot) :
    ∃ p', PermissionUnprot.foreign_write p = .ok p' := by
  cases p <;> exact ⟨_, rfl⟩

/-- `PermissionProt::prevents_deallocation` holds if and only if
`PermissionProt::foreign_write` raises UB, discharging the inline invariant note
in `spec/mem/tree_borrows/state_machine_protected.md`. -/
theorem PermissionProt.prevents_deallocation_iff_foreign_write_err (p : Gen.PermissionProt) :
    PermissionProt.prevents_deallocation p = true ↔
      ∃ msg, PermissionProt.foreign_write p = .error (.ub msg) := by
  cases p with
  | Reserved hl hf =>
    cases hl <;> simp [PermissionProt.prevents_deallocation, PermissionProt.foreign_write, ub]
  | Frozen hl =>
    cases hl <;> simp [PermissionProt.prevents_deallocation, PermissionProt.foreign_write, ub]
  | Unique | Disabled | Cell =>
    simp [PermissionProt.prevents_deallocation, PermissionProt.foreign_write, ub]

/-- Combined `Permission::prevents_deallocation` holds if and only if a foreign
write transition (`Permission::transition p .Write .Foreign`) raises UB
(`spec/mem/tree_borrows/state_machine.md`). -/
theorem Permission.prevents_deallocation_iff_foreign_write_err (p : Gen.Permission) :
    Permission.prevents_deallocation p = true ↔
      ∃ msg, Permission.transition p .Write .Foreign = .error (.ub msg) := by
  cases p with
  | Unprot u =>
    obtain ⟨u', hu'⟩ := PermissionUnprot.foreign_write_ok u
    simp [Permission.prevents_deallocation, PermissionUnprot.prevents_deallocation,
      Permission.transition, PermissionUnprot.transition, hu', pure, Except.pure, bind, Except.bind]
  | Prot pr =>
    simp only [Permission.prevents_deallocation, Permission.transition, PermissionProt.transition,
      PermissionProt.prevents_deallocation_iff_foreign_write_err]
    constructor
    · rintro ⟨msg, h⟩
      exact ⟨msg, by simp [h, bind, Except.bind]⟩
    · rintro ⟨msg, h⟩
      cases hfw : PermissionProt.foreign_write pr with
      | ok pr' => simp [hfw, pure, Except.pure, bind, Except.bind] at h
      | error e =>
        simp [hfw, bind, Except.bind] at h
        subst h
        exact ⟨msg, rfl⟩

/-- `Permission::transition` preserves `Permission::matches_protector` across all
access kinds and node relations (`spec/mem/tree_borrows/state_machine.md`). -/
theorem Permission.transition_preserves_matches_protector
    {p p' : Gen.Permission} {prot : Gen.Protected} {kind : Gen.AccessKind} {rel : Gen.NodeRelation}
    (hm : Permission.matches_protector p prot = true)
    (ht : Permission.transition p kind rel = .ok p') :
    Permission.matches_protector p' prot = true := by
  cases p with
  | Unprot u =>
    cases hp : PermissionUnprot.transition u kind rel with
    | error e => simp [Permission.transition, hp, bind, Except.bind] at ht
    | ok u' =>
      simp [Permission.transition, hp, pure, Except.pure, bind, Except.bind] at ht
      subst ht
      simpa [Permission.matches_protector] using hm
  | Prot pr =>
    cases hp : PermissionProt.transition pr kind rel with
    | error e => simp [Permission.transition, hp, bind, Except.bind] at ht
    | ok pr' =>
      simp [Permission.transition, hp, pure, Except.pure, bind, Except.bind] at ht
      subst ht
      simpa [Permission.matches_protector] using hm

/-- Every permission returned by `ReborrowSettings::perm` satisfies
`Permission::matches_protector` for the target `Protected` mode
(`spec/mem/tree_borrows/reborrow_settings.md`). -/
theorem ReborrowSettings.perm_matches_protector
    {ptrTy : Gen.PtrType} {prot : Gen.Protected} {iw inside frozen : Bool} {p : Gen.Permission}
    (hp : ReborrowSettings.perm ptrTy prot iw inside frozen = .ok p) :
    Permission.matches_protector p prot = true := by
  unfold ReborrowSettings.perm at hp
  cases ptrTy with
  | Ref mutbl pointee =>
    cases mutbl with
    | Immutable =>
      cases frozen <;> cases hprot : Protected.yes prot <;>
        simp [hprot, pure, Except.pure] at hp <;> subst hp <;>
        simp [Permission.matches_protector, hprot]
    | Mutable =>
      cases hiw : (iw && inside) with
      | true =>
        cases hprot : Protected.yes prot <;>
          simp [hiw, hprot, pure, Except.pure, specPanic] at hp
        subst hp
        simp [Permission.matches_protector, hprot]
      | false =>
        cases frozen <;> cases hprot : Protected.yes prot <;>
          simp [hiw, hprot, pure, Except.pure] at hp <;> subst hp <;>
          simp [Permission.matches_protector, hprot]
  | Box pointee =>
    cases hiw : (iw && inside) with
    | true =>
      cases hprot : Protected.yes prot <;>
        simp [hiw, hprot, pure, Except.pure, specPanic] at hp
      subst hp
      simp [Permission.matches_protector, hprot]
    | false =>
      cases frozen <;> cases hprot : Protected.yes prot <;>
        simp [hiw, hprot, pure, Except.pure] at hp <;> subst hp <;>
        simp [Permission.matches_protector, hprot]
  | Raw _ | FnPtr | VTablePtr _ =>
    simp [specPanic] at hp

private theorem mapM_loop_forall {α β : Type} {f : α → Interp β} {P : β → Prop}
    (hf : ∀ a b, f a = .ok b → P b) :
    ∀ (xs : List α) (acc : List β),
      (∀ y ∈ acc, P y) →
      ∀ ys, List.mapM.loop f xs acc = .ok ys → ∀ y ∈ ys, P y
  | [], acc, hacc, ys, h => by
    simp [List.mapM.loop, pure, Except.pure] at h
    subst h
    intro y hy
    exact hacc y (List.mem_reverse.mp hy)
  | x :: xs, acc, hacc, ys, h => by
    simp only [List.mapM.loop] at h
    cases hx : f x with
    | error _ => rw [hx] at h; cases h
    | ok b =>
      rw [hx] at h
      dsimp only [bind, Except.bind] at h
      refine mapM_loop_forall hf xs (b :: acc) ?_ ys h
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hmem
      · exact hf x y hx
      · exact hacc y hmem

/-- Whenever `ReborrowSettings::new` returns `Some(s)`, both `s.outside` and
every byte permission in `s.inside` match `s.protected`, guaranteeing that
`TreeBorrowsMemory::reborrow`'s `matches_protector` assertion never panics
(`spec/mem/tree_borrows/{reborrow_settings,memory}.md`). -/
theorem ReborrowSettings.new_matches_protector {Provenance : Type}
    {lookup : Gen.ThinPointer Provenance → Interp Gen.VTable}
    {ptr : Gen.Pointer Provenance} {ptrTy : Gen.PtrType}
    {fnEntry : Bool} {params : Gen.TreeBorrowsParams} {fnIw : Bool}
    {s : Gen.ReborrowSettings}
    (hnew : ReborrowSettings.new lookup ptr ptrTy fnEntry params fnIw = .ok (some s)) :
    Permission.matches_protector s.outside s.«protected» = true ∧
      ∀ p ∈ s.inside, Permission.matches_protector p s.«protected» = true := by
  unfold ReborrowSettings.new at hnew
  have hunpin_body :
      ∀ info : Gen.PointeeInfo,
        PtrType.safe_pointee ptrTy = some info →
        (do
          let prot : Gen.Protected :=
            if fnEntry then match ptrTy with | .Box _ => .Weak | _ => .Strong else .No
          let iw : Bool := Protected.yes prot && params.implicit_writes && fnIw
          let freezeMask ←
            UnsafeCellStrategy.freeze_mask lookup info.unsafe_cells info.layout ptr.metadata
          let inside ← freezeMask.mapM (fun freeze =>
            ReborrowSettings.perm ptrTy prot iw true freeze)
          let outside ← ReborrowSettings.perm ptrTy prot iw false info.freeze
          pure (some { inside := inside, outside := outside, «protected» := prot } :
            Option Gen.ReborrowSettings)) = .ok (some s) →
        Permission.matches_protector s.outside s.«protected» = true ∧
          ∀ p ∈ s.inside, Permission.matches_protector p s.«protected» = true := by
    intro info _ hh
    cases hmask : UnsafeCellStrategy.freeze_mask lookup info.unsafe_cells info.layout ptr.metadata with
    | error _ => rw [hmask] at hh; cases hh
    | ok mask =>
      rw [hmask] at hh
      dsimp only [bind, Except.bind] at hh
      generalize hin : List.mapM (m := Interp) _ mask = inRes at hh
      cases inRes with
      | error _ => cases hh
      | ok inside =>
        dsimp only at hh
        generalize hout : ReborrowSettings.perm ptrTy _ _ false info.freeze = outRes at hh
        cases outRes with
        | error _ => cases hh
        | ok outside =>
          dsimp only [pure, Except.pure] at hh
          injection hh with hsome
          injection hsome with hs
          rw [← hs]
          refine ⟨ReborrowSettings.perm_matches_protector hout, ?_⟩
          exact mapM_loop_forall (fun _ _ hp => ReborrowSettings.perm_matches_protector hp)
            mask [] (by intro _ h; cases h) inside hin
  cases ptrTy with
  | Raw _ | FnPtr | VTablePtr _ => cases hnew
  | Ref mutbl info =>
    cases mutbl with
    | Immutable => exact hunpin_body info rfl hnew
    | Mutable =>
      dsimp only [PtrType.safe_pointee] at hnew
      cases hu : info.unpin <;> simp only [hu, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hnew
      · cases hnew
      · exact hunpin_body info rfl hnew
  | Box info =>
    dsimp only [PtrType.safe_pointee] at hnew
    cases hu : info.unpin <;> simp only [hu, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hnew
    · cases hnew
    · exact hunpin_body info rfl hnew

/-- On any permission matching a live (`Protected.yes prot = true`) protector,
`Permission::unprotect` succeeds without panicking and yields an unprotected
permission matching `Protected::No`, guaranteeing `TreeBorrowsMemory::release_protector`'s
`Permission::unprotect` step never panics (`spec/mem/tree_borrows/{state_machine,memory}.md`). -/
theorem Permission.unprotect_matches_no
    {p : Gen.Permission} {prot : Gen.Protected}
    (hm : Permission.matches_protector p prot = true)
    (hyes : Protected.yes prot = true) :
    ∃ p' acc, Permission.unprotect p = .ok (p', acc) ∧
      Permission.matches_protector p' .No = true := by
  cases p with
  | Unprot _ => simp [Permission.matches_protector, hyes] at hm
  | Prot pr =>
    refine ⟨.Unprot (PermissionProt.unprotect pr).1, (PermissionProt.unprotect pr).2, rfl, ?_⟩
    simp [Permission.matches_protector, Protected.yes]

/-! ## Unconditional equivalence of polymorphic `Machine<BM>` and `Mach` (`spec/lang/machine.md`) -/

private theorem bind_congr {α β : Type} {x y : Interp α} {f g : α → Interp β}
    (hxy : x = y) (hfg : ∀ a, f a = g a) :
    (x >>= f) = (y >>= g) := by
  subst hxy
  cases x with
  | error _ => rfl
  | ok a => exact hfg a

private theorem bind_congr_right {α β : Type} (x : Interp α) {f g : α → Interp β}
    (hfg : ∀ a, f a = g a) :
    (x >>= f) = (x >>= g) :=
  bind_congr rfl hfg

private theorem find?_eq_of_eq {α : Type} {p q : α → Bool} (h : ∀ x, p x = q x) :
    ∀ xs : List α, xs.find? p = xs.find? q
  | [] => rfl
  | x :: xs => by
    simp only [List.find?, h x]
    cases q x
    · exact find?_eq_of_eq h xs
    · rfl

private theorem filter_eq_of_eq {α : Type} {p q : α → Bool} (h : ∀ x, p x = q x) :
    ∀ xs : List α, xs.filter p = xs.filter q
  | [] => rfl
  | x :: xs => by
    simp only [List.filter, h x]
    cases q x
    · exact filter_eq_of_eq h xs
    · exact congrArg (x :: ·) (filter_eq_of_eq h xs)

private theorem map_eq_of_eq {α β : Type} {f g : α → β} (h : ∀ x, f x = g x) :
    ∀ xs : List α, xs.map f = xs.map g
  | [] => rfl
  | x :: xs => by simp only [List.map, h x, map_eq_of_eq h xs]

private theorem abstractByte_dataM_bm_eq :
    AbstractByte.dataM (Provenance := Prov) = AbstractByte.data := by
  funext b; cases b <;> rfl

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

mutual

private theorem decodeDiscriminantM_bm_eq {σ : Type}
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

private theorem decodeDiscriminantChildrenM_bm_eq {σ : Type}
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

private theorem encodeDiscriminantM_bm_eq {σ : Type}
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

private theorem checkPtrMetadataM_bm_eq (pm : Option (Gen.PointerMeta Prov))
    (kind : Gen.PointerMetaKind) :
    checkPtrMetadataM pm kind = checkPtrMetadata pm kind := by
  unfold checkPtrMetadataM checkPtrMetadata
  rcases pm with _ | (_ | _) <;> cases kind <;> rfl

private theorem cm_dereferenceable_bm_eq (cm : Gen.ConcurrentMemory BM) (ptr : Ptr) (sz : Size) :
    ConcurrentMemory.dereferenceable (M := BM) cm ptr sz =
      CM.dereferenceable cm ptr sz := rfl

private theorem checkPtrM_bm_eq (ptr : Gen.Pointer Prov) (ptrTy : Gen.PtrType)
    (m : Option Mach) :
    checkPtrM (M := BM) ptr ptrTy m = checkPtr ptr ptrTy m := by
  unfold checkPtrM checkPtr
  refine bind_congr_right _ (fun _ => ?_)
  refine bind_congr (checkPtrMetadataM_bm_eq _ _) (fun _ => ?_)
  cases PtrType.safe_pointee ptrTy with
  | none => cases ptrTy <;> rfl
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

private theorem cm_load_bm_eq (cm : Gen.ConcurrentMemory BM) (ptr : Ptr) (len : Size)
    (align : Align) (atomicity : Gen.Atomicity) :
    ConcurrentMemory.load (M := BM) cm ptr len align atomicity =
      CM.load cm ptr len align atomicity := rfl

private theorem cm_store_bm_eq (cm : Gen.ConcurrentMemory BM) (ptr : Ptr) (bs : List Byte)
    (align : Align) (atomicity : Gen.Atomicity) :
    ConcurrentMemory.store (M := BM) cm ptr bs align atomicity =
      CM.store cm ptr bs align atomicity := rfl

private theorem cm_deinit_bm_eq (cm : Gen.ConcurrentMemory BM) (ptr : Ptr) (len : Size)
    (align : Align) :
    ConcurrentMemory.deinit (M := BM) cm ptr len align =
      CM.deinit cm ptr len align := rfl

private theorem cm_signed_deref_bm_eq (cm : Gen.ConcurrentMemory BM) (ptr : Ptr) (off : Int) :
    ConcurrentMemory.signed_dereferenceable (M := BM) cm ptr off =
      CM.signed_dereferenceable cm ptr off := rfl

private theorem cm_allocate_bm_eq (cm : Gen.ConcurrentMemory BM) (kind : Gen.AllocationKind)
    (size : Size) (align : Align) :
    ConcurrentMemory.allocate (M := BM) cm kind size align =
      CM.allocate cm kind size align := by
  unfold ConcurrentMemory.allocate CM.allocate MemoryOps.allocate instMemoryOpsBM
  rfl

private theorem cm_deallocate_bm_eq (cm : Gen.ConcurrentMemory BM) (ptr : Ptr)
    (kind : Gen.AllocationKind) (size : Size) (align : Align) :
    ConcurrentMemory.deallocate (M := BM) cm ptr kind size align =
      CM.deallocate cm ptr kind size align := rfl

private theorem cm_check_data_races_bm_eq (cm : Gen.ConcurrentMemory BM) (tid : Gen.ThreadId)
    (prev : Set Gen.ThreadId × List Gen.Access) :
    ConcurrentMemory.check_data_races (M := BM) cm tid prev =
      CM.check_data_races cm tid prev := rfl

private theorem storageDeadM_bm_eq (fr : Frame) (cm : Gen.ConcurrentMemory BM)
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

private theorem storageLiveM_bm_eq (fr : Frame) (cm : Gen.ConcurrentMemory BM)
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

private theorem computeSizeM_bm_eq (m : Mach) (layout : Gen.LayoutStrategy)
    (pm : Option (Gen.PointerMeta Prov)) :
    computeSizeM (M := BM) m layout pm = computeSize m layout pm := by
  unfold computeSizeM computeSize
  rw [vtableLookupM_bm_eq]

private theorem computeAlignM_bm_eq (m : Mach) (layout : Gen.LayoutStrategy)
    (pm : Option (Gen.PointerMeta Prov)) :
    computeAlignM (M := BM) m layout pm = computeAlign m layout pm := by
  unfold computeAlignM computeAlign
  rw [vtableLookupM_bm_eq]

private theorem typedLoadM_bm_eq (m : Mach) (ptr : Ptr) (ty : Gen.«Type») (align : Align)
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

private theorem typedStoreM_bm_eq (m : Mach) (ptr : Ptr) (val : Val) (ty : Gen.«Type»)
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

private theorem placeLoadM_bm_eq (m : Mach) (place : Gen.Place BM) (ty : Gen.«Type») :
    placeLoadM (M := BM) m place ty = placeLoad m place ty := by
  unfold placeLoadM placeLoad
  rw [typedLoadM_bm_eq]

private theorem placeStoreM_bm_eq (m : Mach) (place : Gen.Place BM) (val : Val) (ty : Gen.«Type») :
    placeStoreM (M := BM) m place val ty = placeStore m place val ty := by
  unfold placeStoreM placeStore
  rw [typedStoreM_bm_eq]

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

private theorem evalUnOpM_bm_eq (op : Gen.UnOp) (arg : Val × Gen.«Type») (m : Option Mach) :
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
  | _ => rfl

private theorem comparePtrM_bm_eq (lp rp : Gen.Pointer Prov) :
    comparePtrM lp rp = comparePtr lp rp := by
  unfold comparePtrM comparePtr
  rcases lp.metadata with _ | (_ | _) <;> rcases rp.metadata with _ | (_ | _) <;> rfl

private theorem evalRelOpM_bm_eq (relOp : Gen.RelOp) (ord : Ordering) :
    evalRelOpM (M := BM) relOp ord = evalRelOp relOp ord := by
  cases relOp <;> cases ord <;> rfl

private theorem evalBinOpM_bm_eq (op : Gen.BinOp) (l r : Val × Gen.«Type») :
    evalBinOpM (M := BM) op l r = evalBinOp op l r := by
  rcases l with ⟨lv, lty⟩
  rcases r with ⟨rv, rty⟩
  unfold evalBinOpM evalBinOp
  cases op with
  | Int _ =>
    cases lv with
    | Int _ =>
      cases lty with
      | Int _ =>
        cases rv with
        | Int _ => rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | IntWithOverflow _ =>
    cases lv with
    | Int _ =>
      cases lty with
      | Int _ =>
        cases rv with
        | Int _ => rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | Rel relOp =>
    cases lty with
    | Int _ =>
      cases lv with
      | Int l =>
        cases rv with
        | Int r => rfl
        | _ => rfl
      | _ => rfl
    | Bool =>
      cases lv with
      | Bool l =>
        cases rv with
        | Bool r => rfl
        | _ => rfl
      | _ => rfl
    | Ptr _ =>
      cases lv with
      | Ptr lp =>
        cases rv with
        | Ptr rp =>
          dsimp only
          exact bind_congr (comparePtrM_bm_eq lp rp) (fun ord =>
            congrArg pure (evalRelOpM_bm_eq relOp ord))
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

private theorem ptrOffsetWrappingM_bm_eq (ptr : Ptr) (off : Int) :
    ptrOffsetWrappingM ptr off = ptrOffsetWrapping ptr off := by
  cases ptr; rfl

private theorem ptrOffsetInboundsM_bm_eq (m : Mach) (ptr : Ptr) (off : Int) :
    ptrOffsetInboundsM (M := BM) m ptr off = ptrOffsetInbounds m ptr off := by
  unfold ptrOffsetInboundsM ptrOffsetInbounds
  exact bind_congr (cm_signed_deref_bm_eq m.mem ptr off) (fun _ => rfl)

private theorem evalPtrOffsetM_bm_eq (m : Mach) (inbounds : Bool) (l r : Val × Gen.«Type») :
    evalPtrOffsetM (M := BM) m inbounds l r = evalPtrOffset m inbounds l r := by
  rcases l with ⟨lv, lty⟩
  rcases r with ⟨rv, rty⟩
  unfold evalPtrOffsetM evalPtrOffset
  cases lv with
  | Ptr lp =>
    rcases lp with ⟨left, _ | _⟩
    · cases rv with
      | Int right =>
        cases inbounds with
        | false => dsimp only [ptrOffsetWrappingM_bm_eq]; rfl
        | true =>
          dsimp only
          exact bind_congr (ptrOffsetInboundsM_bm_eq m left right) (fun _ => rfl)
      | _ => rfl
    · rfl
  | _ => rfl

private theorem evalPtrOffsetFromM_bm_eq (m : Mach) (inbounds nonneg : Bool)
    (l r : Val × Gen.«Type») :
    evalPtrOffsetFromM (M := BM) m inbounds nonneg l r = evalPtrOffsetFrom m inbounds nonneg l r := by
  rcases l with ⟨lv, lty⟩
  rcases r with ⟨rv, rty⟩
  unfold evalPtrOffsetFromM evalPtrOffsetFrom
  cases lv with
  | Ptr lp =>
    rcases lp with ⟨left, _ | _⟩
    · cases rv with
      | Ptr rp =>
        rcases rp with ⟨right, _ | _⟩
        · dsimp only
          cases inbounds with
          | false => rfl
          | true =>
            refine bind_congr (cm_signed_deref_bm_eq m.mem left (-(left.addr - right.addr))) (fun _ => ?_)
            exact bind_congr (cm_signed_deref_bm_eq m.mem right (left.addr - right.addr)) (fun _ => rfl)
        · rfl
      | _ => rfl
    · rfl
  | _ => rfl

private theorem dropLast_append_getLast_cons {α : Type} :
    ∀ (x : α) (xs : List α),
      (x :: xs).dropLast ++ [(x :: xs).getLast (by simp)] = x :: xs
  | _, [] => rfl
  | x, y :: ys => by
    show x :: ((y :: ys).dropLast ++ [(y :: ys).getLast (by simp)]) = x :: y :: ys
    rw [dropLast_append_getLast_cons y ys]

private theorem curFrameM_bm_eq (m : Mach) :
    curFrameM (M := BM) m = curFrame m := by
  unfold curFrameM curFrame activeThreadM activeThread
  exact bind_congr_right _ (fun t => by cases t.stack.getLast? <;> rfl)

private theorem mutateCurFrameM_bm_eq (m : Mach) (f : Frame → Frame) :
    mutateCurFrameM (M := BM) m f = mutateCurFrame m f := by
  unfold mutateCurFrameM mutateCurFrame activeThreadM activeThread
  refine bind_congr_right _ (fun t => ?_)
  cases t.stack.getLast? with
  | none => rfl
  | some fr => exact bind_congr_right _ (fun _ => rfl)

private theorem tryMutateCurFrameM_bm_eq (m : Mach)
    (f g : Frame → Gen.ConcurrentMemory BM → Interp (Frame × Gen.ConcurrentMemory BM))
    (hfg : ∀ fr cm, f fr cm = g fr cm) :
    tryMutateCurFrameM (M := BM) m f = tryMutateCurFrame m g := by
  unfold tryMutateCurFrameM tryMutateCurFrame activeThreadM activeThread
  refine bind_congr_right _ (fun t => ?_)
  cases t.stack.getLast? with
  | none => rfl
  | some fr =>
    dsimp only
    exact bind_congr (hfg fr m.mem) (fun ⟨_, _⟩ => bind_congr_right _ (fun _ => rfl))

private theorem jumpToBlockM_bm_eq (m : Mach) (b : Gen.BbName) :
    jumpToBlockM (M := BM) m b = jumpToBlock m b :=
  mutateCurFrameM_bm_eq m _

/-- On `M = BM`, `mutateCurFrameOutM` wrapping `ConcurrentMemory.retag_ptr`
reduces unconditionally to `(retagPtrBM m ptr).map (·, m)` for every `m : Mach`. -/
theorem mutateCurFrameOutM_retag_bm_eq (m : Mach) (ptr : Gen.Pointer Prov)
    (ptrTy : Gen.PtrType) (fnEntry : Bool) (iw : Gen.StackFrame BM → Bool) :
    mutateCurFrameOutM (M := BM) m (fun fr cm => do
      let (ptr', cm', extra') ←
        ConcurrentMemory.retag_ptr cm fr.extra ptr ptrTy fnEntry (iw fr) (vtableLookupM m)
      pure (ptr', { fr with extra := extra' }, cm')) =
    (do let ptr' ← retagPtrBM m ptr; pure (ptr', m)) := by
  unfold mutateCurFrameOutM retagPtrBM listIndex
  by_cases hnonneg : 0 ≤ m.active_thread
  · simp only [hnonneg, ↓reduceIte]
    cases hget : m.threads[m.active_thread.toNat]? with
    | none => rfl
    | some t =>
      dsimp only [pure, Except.pure, bind, Except.bind]
      cases hst : t.stack with
      | nil => rfl
      | cons hd tl =>
        have hlast : (hd :: tl).getLast? = some ((hd :: tl).getLast (by simp)) :=
          List.getLast?_eq_some_getLast (by simp)
        have hdrop : (hd :: tl).dropLast ++ [(hd :: tl).getLast (by simp)] = hd :: tl :=
          dropLast_append_getLast_cons hd tl
        obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.mp hget
        have ht_self : ({ t with stack := hd :: tl } : Gen.Thread BM) = t := by
          cases t; simp at hst; subst hst; rfl
        have hset : listSet m.threads m.active_thread t "mutate_at" = .ok m.threads := by
          unfold listSet
          have hcond : 0 ≤ m.active_thread ∧ m.active_thread.toNat < m.threads.length :=
            ⟨hnonneg, hlt⟩
          simp [hcond, ← hval, List.set_getElem_self, pure, Except.pure]
        simp only [hlast, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
          ConcurrentMemory.retag_ptr, MemoryOps.retag_ptr,
          pure, Except.pure, bind, Except.bind, hdrop, ht_self, hset]
  · simp only [hnonneg, ↓reduceIte, bind, Except.bind, specPanic]

private theorem evalConstantM_bm_eq (m : Mach) (c : Gen.Constant) :
    evalConstantM (M := BM) m c = evalConstant m c := by
  cases c <;> rfl

mutual

theorem evalPlaceM_bm_eq :
    ∀ (m : Mach) (pe : Gen.PlaceExpr),
      evalPlaceM (M := BM) m pe = evalPlace m pe
  | m, .Local name => by
    unfold evalPlaceM evalPlace
    rw [curFrameM_bm_eq]
    cases curFrame m with
    | error _ => rfl
    | ok fr =>
      dsimp only [bind, Except.bind]
      cases mapIndex fr.func.locals name "self.cur_frame().func.locals[name]" with
      | error _ => rfl
      | ok _ =>
        dsimp only [bind, Except.bind]
        cases mapGet fr.locals name <;> rfl
  | m, .Field root field => by
    unfold evalPlaceM evalPlace
    refine bind_congr (evalPlaceM_bm_eq m root) (fun ⟨⟨rootPl, ty⟩, m1⟩ => ?_)
    dsimp only
    have htail : ∀ (p : Gen.Offset × Gen.«Type»),
        (show Interp ((Gen.Place BM × Gen.«Type») × Mach) from do
          let rlay ← Type.layout ty
          let rootSize ← computeSizeM (M := BM) m1 rlay rootPl.ptr.metadata
          if (!decide (p.1.bytes ≤ rootSize.bytes)) = true then
            specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
          else do
            let ptr ← ptrOffsetInboundsM (M := BM) m1 rootPl.ptr.thin_pointer (p.1.bytes : Int)
            let flay ← Type.layout p.2
            pure ((({ ptr := (if (!LayoutStrategy.is_sized flay) = true then ThinPointer.widen ptr rootPl.ptr.metadata else ThinPointer.widen ptr none), aligned := rootPl.aligned } : Gen.Place BM), p.2), m1)) =
        (show Interp ((Gen.Place BM × Gen.«Type») × Mach) from do
          let rlay ← Type.layout ty
          let rootSize ← computeSize m1 rlay rootPl.ptr.metadata
          if (!decide (p.1.bytes ≤ rootSize.bytes)) = true then
            specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
          else do
            let ptr ← ptrOffsetInbounds m1 rootPl.ptr.thin_pointer (p.1.bytes : Int)
            let flay ← Type.layout p.2
            pure ((({ ptr := (if (!LayoutStrategy.is_sized flay) = true then ThinPointer.widen ptr rootPl.ptr.metadata else ThinPointer.widen ptr none), aligned := rootPl.aligned } : Gen.Place BM), p.2), m1)) := by
      intro p
      refine bind_congr_right _ (fun rlay => ?_)
      refine bind_congr (computeSizeM_bm_eq m1 rlay rootPl.ptr.metadata) (fun _ => ?_)
      split
      · rfl
      · exact bind_congr (ptrOffsetInboundsM_bm_eq m1 rootPl.ptr.thin_pointer _) (fun _ =>
          bind_congr_right _ (fun _ => rfl))
    cases ty with
    | Tuple sizedFields sizedHeadLayout unsizedField =>
      dsimp only
      split
      · exact bind_congr_right _ htail
      · split
        · cases unsizedField with
          | none => rfl
          | some tailTy =>
            dsimp only
            exact bind_congr_right _ (fun tlay =>
              bind_congr (computeAlignM_bm_eq m1 tlay rootPl.ptr.metadata) (fun tailAlign => by
                dsimp only [pure, Except.pure, bind, Except.bind]
                exact htail (TupleHeadLayout.tail_offset sizedHeadLayout tailAlign, tailTy)))
        · rfl
    | Union _ _ _ _ => dsimp only; exact bind_congr_right _ htail
    | _ => rfl
  | m, .Index root index => by
    unfold evalPlaceM evalPlace
    refine bind_congr (evalPlaceM_bm_eq m root) (fun ⟨⟨rootPl, ty⟩, m1⟩ => ?_)
    dsimp only
    refine bind_congr (evalValueM_bm_eq m1 index) (fun ⟨⟨idxVal, _⟩, m2⟩ => ?_)
    dsimp only
    have htail : ∀ (pm : Option (Gen.PointerMeta Prov)) (idx : Int) (p : Gen.«Type» × Int),
        (if idx < 0 ∨ idx ≥ p.2 then ub "access to out-of-bounds index"
         else do
           let elemLayout ← Type.layout p.1
           let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array & slice elements are sized"
           let offset ← Size.mulInt elemSize idx
           let rlay ← Type.layout ty
           let rootSize ← computeSizeM (M := BM) m2 rlay pm
           if offset.bytes ≤ rootSize.bytes then do
             let ptr ← ptrOffsetInboundsM (M := BM) m2 rootPl.ptr.thin_pointer (offset.bytes : Int)
             pure ((({ ptr := ThinPointer.widen ptr none, aligned := rootPl.aligned } : Gen.Place BM), p.1), m2)
           else specPanic "sanity check: the indexed offset should not be outside what the type allows.") =
        (if idx < 0 ∨ idx ≥ p.2 then ub "access to out-of-bounds index"
         else do
           let elemLayout ← Type.layout p.1
           let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array & slice elements are sized"
           let offset ← Size.mulInt elemSize idx
           let rlay ← Type.layout ty
           let rootSize ← computeSize m2 rlay pm
           if offset.bytes ≤ rootSize.bytes then do
             let ptr ← ptrOffsetInbounds m2 rootPl.ptr.thin_pointer (offset.bytes : Int)
             pure ((({ ptr := ThinPointer.widen ptr none, aligned := rootPl.aligned } : Gen.Place BM), p.1), m2)
           else specPanic "sanity check: the indexed offset should not be outside what the type allows.") := by
      intro pm idx p
      split
      · rfl
      · apply bind_congr_right; intro _
        apply bind_congr_right; intro _
        apply bind_congr_right; intro _
        apply bind_congr_right; intro rlay
        refine bind_congr (computeSizeM_bm_eq m2 rlay pm) (fun _ => ?_)
        split
        · exact bind_congr (ptrOffsetInboundsM_bm_eq m2 rootPl.ptr.thin_pointer _) (fun _ => rfl)
        · rfl
    cases idxVal with
    | Int i =>
      dsimp only [pure, Except.pure, bind, Except.bind]
      cases ty with
      | Array elem count =>
        dsimp only [pure, Except.pure, bind, Except.bind]
        exact htail rootPl.ptr.metadata i (elem, count)
      | Slice elem =>
        dsimp only
        rcases rootPl.ptr.metadata with _ | (count | _)
        · rfl
        · dsimp only [pure, Except.pure, bind, Except.bind]
          exact htail (some (.ElementCount count)) i (elem, count)
        · rfl
      | _ => rfl
    | _ => rfl
  | m, .Deref operand ty => by
    unfold evalPlaceM evalPlace
    refine bind_congr (evalValueM_bm_eq m operand) (fun ⟨⟨v, vTy⟩, m1⟩ => ?_)
    dsimp only
    cases v with
    | Ptr ptr =>
      cases vTy with
      | Ptr ptrType =>
        dsimp only
        have htail :
            (do
              let lay ← Type.layout ty
              let align ← computeAlignM (M := BM) m1 lay ptr.metadata
              pure ((({ ptr := ptr, aligned := Align.is_aligned align ptr.thin_pointer.addr } : Gen.Place BM), ty), m1)) =
            (do
              let lay ← Type.layout ty
              let align ← computeAlign m1 lay ptr.metadata
              pure ((({ ptr := ptr, aligned := Align.is_aligned align ptr.thin_pointer.addr } : Gen.Place BM), ty), m1)) :=
          bind_congr_right _ (fun lay =>
            bind_congr (computeAlignM_bm_eq m1 lay ptr.metadata) (fun _ => rfl))
        cases PtrType.safe_pointee ptrType with
        | none =>
          dsimp only [pure, Except.pure, bind, Except.bind]
          exact htail
        | some pointee =>
          dsimp only
          refine bind_congr (computeAlignM_bm_eq m1 pointee.layout ptr.metadata) (fun _ => ?_)
          split
          · rfl
          · refine bind_congr (computeSizeM_bm_eq m1 pointee.layout ptr.metadata) (fun pSize => ?_)
            dsimp only [cm_dereferenceable_bm_eq]
            generalize CM.dereferenceable m1.mem ptr.thin_pointer pSize = d
            rcases d with _ | ⟨⟩
            · rfl
            · dsimp only [pure, Except.pure, bind, Except.bind]
              exact htail
      | _ => rfl
    | _ => rfl
  | _, .Downcast _ _ => by unfold evalPlaceM evalPlace; rfl

theorem evalValueM_bm_eq :
    ∀ (m : Mach) (ve : Gen.ValueExpr),
      evalValueM (M := BM) m ve = evalValue m ve
  | m, .Constant c ty => by
    unfold evalValueM evalValue
    rw [evalConstantM_bm_eq]
  | m, .Tuple exprs ty => by
    unfold evalValueM evalValue
    rw [evalValuesM_bm_eq m exprs]
  | m, .Load source => by
    unfold evalValueM evalValue
    rw [evalPlaceM_bm_eq m source]
    rcases evalPlace m source with _ | ⟨⟨place, ty⟩, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [placeLoadM_bm_eq]
  | m, .AddrOf target ptrTy => by
    unfold evalValueM evalValue
    refine bind_congr (evalPlaceM_bm_eq m target) (fun ⟨⟨place, _⟩, m1⟩ => ?_)
    dsimp only
    refine bind_congr (checkValueM_bm_eq (.Ptr place.ptr) (.Ptr ptrTy) (some m1)) (fun _ => ?_)
    rw [mutateCurFrameOutM_retag_bm_eq m1 place.ptr ptrTy false (fun _ => true)]
    cases retagPtrBM m1 place.ptr <;> rfl
  | m, .UnOp operator operand => by
    unfold evalValueM evalValue
    rw [evalValueM_bm_eq m operand]
    rcases evalValue m operand with _ | ⟨arg, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [evalUnOpM_bm_eq]
  | m, .BinOp operator left right => by
    cases operator with
    | PtrOffset inbounds =>
      unfold evalValueM evalValue
      rw [evalValueM_bm_eq m left]
      rcases evalValue m left with _ | ⟨lp, m1⟩
      · rfl
      · dsimp only [bind, Except.bind]
        rw [evalValueM_bm_eq m1 right]
        rcases evalValue m1 right with _ | ⟨rp, m2⟩
        · rfl
        · dsimp only [bind, Except.bind]
          rw [evalPtrOffsetM_bm_eq]
    | PtrOffsetFrom inbounds nonneg =>
      unfold evalValueM evalValue
      rw [evalValueM_bm_eq m left]
      rcases evalValue m left with _ | ⟨lp, m1⟩
      · rfl
      · dsimp only [bind, Except.bind]
        rw [evalValueM_bm_eq m1 right]
        rcases evalValue m1 right with _ | ⟨rp, m2⟩
        · rfl
        · dsimp only [bind, Except.bind]
          rw [evalPtrOffsetFromM_bm_eq]
    | Int iop =>
      unfold evalValueM evalValue
      rw [evalValueM_bm_eq m left]
      rcases evalValue m left with _ | ⟨lp, m1⟩
      · rfl
      · dsimp only [bind, Except.bind]
        rw [evalValueM_bm_eq m1 right]
        rcases evalValue m1 right with _ | ⟨rp, m2⟩
        · rfl
        · dsimp only [bind, Except.bind]
          rw [evalBinOpM_bm_eq]
    | IntWithOverflow iop =>
      unfold evalValueM evalValue
      rw [evalValueM_bm_eq m left]
      rcases evalValue m left with _ | ⟨lp, m1⟩
      · rfl
      · dsimp only [bind, Except.bind]
        rw [evalValueM_bm_eq m1 right]
        rcases evalValue m1 right with _ | ⟨rp, m2⟩
        · rfl
        · dsimp only [bind, Except.bind]
          rw [evalBinOpM_bm_eq]
    | Rel rop =>
      unfold evalValueM evalValue
      rw [evalValueM_bm_eq m left]
      rcases evalValue m left with _ | ⟨lp, m1⟩
      · rfl
      · dsimp only [bind, Except.bind]
        rw [evalValueM_bm_eq m1 right]
        rcases evalValue m1 right with _ | ⟨rp, m2⟩
        · rfl
        · dsimp only [bind, Except.bind]
          rw [evalBinOpM_bm_eq]
    | ConstructWidePointer _ =>
      unfold evalValueM evalValue
      rw [evalValueM_bm_eq m left]
      rcases evalValue m left with _ | ⟨lp, m1⟩
      · rfl
      · dsimp only [bind, Except.bind]
        rw [evalValueM_bm_eq m1 right]
        rcases evalValue m1 right with _ | ⟨rp, m2⟩
        · rfl
        · dsimp only [bind, Except.bind]
          rw [evalBinOpM_bm_eq]
  | _, .Union _ _ _ => by unfold evalValueM evalValue; rfl
  | _, .Variant _ _ _ => by unfold evalValueM evalValue; rfl
  | _, .GetDiscriminant _ => by unfold evalValueM evalValue; rfl

theorem evalValuesM_bm_eq :
    ∀ (m : Mach) (es : List Gen.ValueExpr),
      evalValuesM (M := BM) m es = evalValues m es
  | _, [] => by unfold evalValuesM evalValues; rfl
  | m, e :: es => by
    unfold evalValuesM evalValues
    rw [evalValueM_bm_eq m e]
    rcases evalValue m e with _ | ⟨⟨val, _⟩, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [evalValuesM_bm_eq m1 es]

end

mutual

theorem retagValM_bm_eq :
    ∀ (m : Mach) (fnEntry : Bool) (val : Val) (ty : Gen.«Type»),
      retagValM (M := BM) m fnEntry val ty =
        (do let v' ← retagVal m fnEntry val ty; pure (v', m))
  | m, fnEntry, .Int _, _ => by unfold retagValM retagVal; rfl
  | m, fnEntry, .Bool _, _ => by unfold retagValM retagVal; rfl
  | m, fnEntry, .Union _, _ => by unfold retagValM retagVal; rfl
  | m, fnEntry, .Ptr ptr, .Ptr ptrType => by
    unfold retagValM retagVal
    dsimp only
    have hret := mutateCurFrameOutM_retag_bm_eq m ptr ptrType fnEntry (fun fr => fr.func.implicit_writes)
    rw [hret]
    cases retagPtrBM m ptr <;> rfl
  | m, fnEntry, .Ptr _, .Int _ | m, fnEntry, .Ptr _, .Bool | m, fnEntry, .Ptr _, .Union _ _ _ _
  | m, fnEntry, .Ptr _, .Tuple _ _ _ | m, fnEntry, .Ptr _, .Array _ _
  | m, fnEntry, .Ptr _, .Enum _ _ _ _ _ | m, fnEntry, .Ptr _, .Slice _
  | m, fnEntry, .Ptr _, .TraitObject _ => by unfold retagValM retagVal; rfl
  | m, fnEntry, .Tuple vals, .Tuple sizedFields _ _ => by
    unfold retagValM retagVal
    rw [retagTupleFieldsM_bm_eq m fnEntry vals sizedFields]
    cases retagTupleFields m fnEntry vals sizedFields <;> rfl
  | m, fnEntry, .Tuple vals, .Array elemTy _ => by
    unfold retagValM retagVal
    rw [retagArrayElemsM_bm_eq m fnEntry elemTy vals]
    cases vals.mapM (fun val => retagVal m fnEntry val elemTy) <;> rfl
  | m, fnEntry, .Tuple _, .Int _ | m, fnEntry, .Tuple _, .Bool | m, fnEntry, .Tuple _, .Union _ _ _ _
  | m, fnEntry, .Tuple _, .Ptr _ | m, fnEntry, .Tuple _, .Enum _ _ _ _ _
  | m, fnEntry, .Tuple _, .Slice _ | m, fnEntry, .Tuple _, .TraitObject _ => by
    unfold retagValM retagVal; rfl
  | m, fnEntry, .Variant discriminant data, .Enum variants _ _ _ _ => by
    unfold retagValM retagVal
    cases mapIndex variants discriminant "variants[discriminant]" with
    | error _ => rfl
    | ok variant =>
      dsimp only [bind, Except.bind]
      rw [retagValM_bm_eq m fnEntry data variant.ty]
      cases retagVal m fnEntry data variant.ty <;> rfl
  | m, fnEntry, .Variant _ _, .Int _ | m, fnEntry, .Variant _ _, .Bool
  | m, fnEntry, .Variant _ _, .Union _ _ _ _ | m, fnEntry, .Variant _ _, .Ptr _
  | m, fnEntry, .Variant _ _, .Tuple _ _ _ | m, fnEntry, .Variant _ _, .Array _ _
  | m, fnEntry, .Variant _ _, .Slice _ | m, fnEntry, .Variant _ _, .TraitObject _ => by
    unfold retagValM retagVal; rfl

theorem retagTupleFieldsM_bm_eq :
    ∀ (m : Mach) (fnEntry : Bool) (vals : List Val) (fields : List (Gen.Offset × Gen.«Type»)),
      retagTupleFieldsM (M := BM) m fnEntry vals fields =
        (do let vs' ← retagTupleFields m fnEntry vals fields; pure (vs', m))
  | m, _, [], [] => by unfold retagTupleFieldsM retagTupleFields; rfl
  | _, _, [], _ :: _ => by unfold retagTupleFieldsM retagTupleFields; rfl
  | _, _, _ :: _, [] => by unfold retagTupleFieldsM retagTupleFields; rfl
  | m, fnEntry, val :: vals, (_, ty) :: fields => by
    unfold retagTupleFieldsM retagTupleFields
    rw [retagValM_bm_eq m fnEntry val ty]
    cases retagVal m fnEntry val ty with
    | error _ => rfl
    | ok v' =>
      dsimp only [bind, Except.bind, pure, Except.pure]
      rw [retagTupleFieldsM_bm_eq m fnEntry vals fields]
      cases retagTupleFields m fnEntry vals fields <;> rfl

theorem retagArrayElemsM_bm_eq :
    ∀ (m : Mach) (fnEntry : Bool) (elemTy : Gen.«Type») (vals : List Val),
      retagArrayElemsM (M := BM) m fnEntry elemTy vals =
        (do let vs' ← vals.mapM (fun val => retagVal m fnEntry val elemTy); pure (vs', m))
  | m, _, _, [] => by
    unfold retagArrayElemsM
    rfl
  | m, fnEntry, elemTy, val :: vals => by
    unfold retagArrayElemsM
    rw [retagValM_bm_eq m fnEntry val elemTy]
    have hmapM : ∀ (f : Val → Interp Val) (acc : List Val),
        List.mapM.loop f vals acc =
          (do let tl ← List.mapM.loop f vals []; pure (acc.reverse ++ tl)) := by
      intro f
      induction vals with
      | nil =>
        intro acc
        simp [List.mapM.loop, pure, Except.pure, bind, Except.bind]
      | cons w ws ih =>
        intro acc
        simp only [List.mapM.loop]
        cases f w with
        | error _ => rfl
        | ok w' =>
          dsimp only [bind, Except.bind]
          rw [ih (w' :: acc), ih [w']]
          cases List.mapM.loop f ws [] with
          | error _ => rfl
          | ok tl =>
            simp [pure, Except.pure, bind, Except.bind, List.append_assoc]
    unfold List.mapM
    simp only [List.mapM.loop]
    cases retagVal m fnEntry val elemTy with
    | error _ => rfl
    | ok v' =>
      dsimp only [bind, Except.bind, pure, Except.pure]
      rw [retagArrayElemsM_bm_eq m fnEntry elemTy vals]
      unfold List.mapM
      rw [hmapM _ [v']]
      cases List.mapM.loop (fun v => retagVal m fnEntry v elemTy) vals [] <;> rfl

end

theorem evalStatementM_bm_eq (m : Mach) (stmt : Gen.Statement) :
    evalStatementM (M := BM) m stmt = evalStatement m stmt := by
  cases stmt with
  | Assign dst src =>
    dsimp only [evalStatementM, evalStatement]
    rw [evalPlaceM_bm_eq]
    rcases evalPlace m dst with _ | ⟨⟨place, ty⟩, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [evalValueM_bm_eq]
      rcases evalValue m1 src with _ | ⟨⟨val, _⟩, m2⟩
      · rfl
      · exact placeStoreM_bm_eq m2 place val ty
  | PlaceMention place =>
    dsimp only [evalStatementM, evalStatement]
    rw [evalPlaceM_bm_eq]
  | Validate place fnEntry =>
    dsimp only [evalStatementM, evalStatement]
    rw [evalPlaceM_bm_eq]
    rcases evalPlace m place with _ | ⟨⟨p, ty⟩, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [placeLoadM_bm_eq]
      rcases placeLoad m1 p ty with _ | ⟨val, m2⟩
      · rfl
      · dsimp only [bind, Except.bind]
        rw [retagValM_bm_eq]
        cases retagVal m2 fnEntry val ty with
        | error _ => rfl
        | ok v' =>
          dsimp only [bind, Except.bind, pure, Except.pure]
          exact placeStoreM_bm_eq m2 p v' ty
  | StorageLive local_ =>
    dsimp only [evalStatementM, evalStatement]
    exact tryMutateCurFrameM_bm_eq m _ _ (fun fr cm => storageLiveM_bm_eq fr cm local_)
  | StorageDead local_ =>
    dsimp only [evalStatementM, evalStatement]
    exact tryMutateCurFrameM_bm_eq m _ _ (fun fr cm => storageDeadM_bm_eq fr cm local_)
  | Deinit place =>
    dsimp only [evalStatementM, evalStatement]
    rw [evalPlaceM_bm_eq]
    rcases evalPlace m place with _ | ⟨⟨p, ty⟩, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      split
      · rfl
      · cases Type.layout ty with
        | error _ => rfl
        | ok lay =>
          dsimp only [bind, Except.bind]
          cases LayoutStrategy.expect_size lay "WF ensures deinits are sized" with
          | error _ => rfl
          | ok sz =>
            dsimp only [bind, Except.bind, cm_deinit_bm_eq]
  | _ => rfl

private theorem deallocAllM_bm_eq :
    ∀ (fuel : Nat) (fr : Frame) (cm : Gen.ConcurrentMemory BM),
      deallocAllM (M := BM) fuel fr cm = deallocAll fuel fr cm
  | 0, fr, cm => by
    unfold deallocAllM deallocAll
    rcases fr.locals.entries with _ | ⟨⟨_, _⟩, _⟩ <;> rfl
  | fuel + 1, fr, cm => by
    unfold deallocAllM deallocAll
    rcases fr.locals.entries with _ | ⟨⟨local_, _⟩, _⟩
    · rfl
    · dsimp only
      rw [storageDeadM_bm_eq]
      rcases storageDead fr cm local_ with _ | ⟨fr', cm'⟩
      · rfl
      · exact deallocAllM_bm_eq fuel fr' cm'

private theorem evalArgsM_bm_eq :
    ∀ (m : Mach) (es : List Gen.ValueExpr),
      evalArgsM (M := BM) m es = evalArgs m es
  | _, [] => rfl
  | m, e :: es => by
    unfold evalArgsM evalArgs
    rw [evalValueM_bm_eq m e]
    rcases evalValue m e with _ | ⟨arg, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [evalArgsM_bm_eq m1 es]

private theorem mutateCurStackM_bm_eq {α : Type} (m : Mach)
    (f : List Frame → Interp (α × List Frame)) :
    mutateCurStackM (M := BM) m f = mutateCurStack m f := rfl

private theorem fnFromPtrM_bm_eq (m : Mach) (v : Val) :
    fnFromPtrM (M := BM) m v = fnFromPtr m v := by
  cases v with
  | Ptr p =>
    rcases p with ⟨thinPtr, metadata⟩
    simp only [fnFromPtrM, fnFromPtr]
    split
    · rfl
    · split <;> split <;> simp_all
  | _ => rfl

private theorem prepareForInplacePassingM_bm_eq (m : Mach) (place : Gen.Place BM)
    (ty : Gen.«Type») :
    prepareForInplacePassingM (M := BM) m place ty = prepareForInplacePassing m place ty := by
  unfold prepareForInplacePassingM prepareForInplacePassing
  refine bind_congr_right _ (fun _ => ?_)
  refine bind_congr_right _ (fun sz => ?_)
  refine bind_congr_right _ (fun _ => ?_)
  refine bind_congr_right _ (fun al => ?_)
  exact bind_congr (cm_deinit_bm_eq m.mem place.ptr.thin_pointer sz al) (fun _ => rfl)

private theorem evalArgumentM_bm_eq (m : Mach) (arg : Gen.ArgumentExpr) :
    evalArgumentM (M := BM) m arg = evalArgument m arg := by
  cases arg with
  | ByValue v =>
    unfold evalArgumentM evalArgument
    exact evalValueM_bm_eq m v
  | InPlace p =>
    unfold evalArgumentM evalArgument
    refine bind_congr (evalPlaceM_bm_eq m p) (fun ⟨⟨place, ty⟩, m1⟩ => ?_)
    dsimp only
    refine bind_congr (placeLoadM_bm_eq m1 place ty) (fun ⟨v, m2⟩ => ?_)
    dsimp only
    exact bind_congr (prepareForInplacePassingM_bm_eq m2 place ty) (fun _ => rfl)

private theorem evalArgumentsM_bm_eq :
    ∀ (m : Mach) (args : List Gen.ArgumentExpr),
      evalArgumentsM (M := BM) m args = evalArguments m args
  | m, [] => by unfold evalArgumentsM evalArguments; rfl
  | m, a :: as => by
    unfold evalArgumentsM evalArguments
    refine bind_congr (evalArgumentM_bm_eq m a) (fun ⟨v, m1⟩ => ?_)
    dsimp only
    exact bind_congr (evalArgumentsM_bm_eq m1 as) (fun _ => rfl)

private theorem allocFrameArgsM_bm_eq :
    ∀ (fr : Frame) (cm : Gen.ConcurrentMemory BM) (ls : List Gen.LocalName),
      allocFrameArgsM (M := BM) fr cm ls = allocFrameArgs fr cm ls
  | fr, cm, [] => by unfold allocFrameArgsM allocFrameArgs; rfl
  | fr, cm, l :: ls => by
    unfold allocFrameArgsM allocFrameArgs
    refine bind_congr (storageLiveM_bm_eq fr cm l) (fun ⟨fr1, cm1⟩ => ?_)
    exact allocFrameArgsM_bm_eq fr1 cm1 ls

private theorem initFrameArgsM_bm_eq :
    ∀ (m : Mach) (frame : Frame) (ls : List Gen.LocalName) (args : List (Val × Gen.«Type»)),
      initFrameArgsM (M := BM) m frame ls args = initFrameArgs m frame ls args
  | m, frame, [], args => by unfold initFrameArgsM initFrameArgs; rfl
  | m, frame, _ :: _, [] => by unfold initFrameArgsM initFrameArgs; rfl
  | m, frame, l :: ls, (v, ty) :: args => by
    have ih : ∀ m', initFrameArgsM (M := BM) m' frame ls args = initFrameArgs m' frame ls args :=
      fun m' => initFrameArgsM_bm_eq m' frame ls args
    unfold initFrameArgsM initFrameArgs
    simp only [typedStoreM_bm_eq, ih]
    refine bind_congr_right _ (fun calleeTy => ?_)
    refine bind_congr_right _ (fun b => ?_)
    split
    · rfl
    · refine bind_congr_right _ (fun l => ?_)
      refine bind_congr_right _ (fun align => ?_)
      refine bind_congr_right _ (fun calleePtr => ?_)
      cases typedStore m calleePtr v ty align .None with
      | ok m' => rfl
      | error e => cases e <;> rfl

private theorem createFrameM_bm_eq (m : Mach) (func : Gen.Function)
    (spa : Gen.StackPopAction BM) (conv : Gen.CallingConvention) (retTy : Gen.«Type»)
    (args : List (Val × Gen.«Type»)) :
    createFrameM (M := BM) m func spa conv retTy args = createFrame m func spa conv retTy args := by
  unfold createFrameM createFrame
  refine bind_congr (storageLiveM_bm_eq _ m.mem func.ret) (fun ⟨fr1, cm1⟩ => ?_)
  dsimp only
  refine bind_congr (allocFrameArgsM_bm_eq fr1 cm1 func.args) (fun ⟨fr2, cm2⟩ => ?_)
  dsimp only
  split
  · rfl
  · refine bind_congr_right _ (fun _ => ?_)
    refine bind_congr_right _ (fun _ => ?_)
    split
    · rfl
    · split
      · rfl
      · exact bind_congr (initFrameArgsM_bm_eq _ fr2 func.args args) (fun _ => rfl)

private theorem evalCallM_bm_eq (m : Mach) (callee : Gen.Function) (conv : Gen.CallingConvention)
    (args : List (Val × Gen.«Type»)) (ret : Gen.Place BM × Gen.«Type»)
    (nb ub : Option Gen.BbName) :
    evalCallM (M := BM) m callee conv args ret nb ub = evalCall m callee conv args ret nb ub := by
  unfold evalCallM evalCall
  refine bind_congr (createFrameM_bm_eq _ _ _ _ _ _) (fun ⟨fr, m1⟩ => ?_)
  dsimp only
  exact bind_congr (mutateCurStackM_bm_eq m1 _) (fun _ => rfl)

private theorem machineExitM_bm_eq {α : Type} (m : Mach) :
    machineExitM (M := BM) (α := α) m = machineExit m := rfl

private theorem cm_allocate_bm_fun :
    @ConcurrentMemory.allocate BM _ _ = CM.allocate := by
  funext cm kind size align
  exact cm_allocate_bm_eq cm kind size align

private theorem cm_deallocate_bm_fun :
    @ConcurrentMemory.deallocate BM _ _ = CM.deallocate := by
  funext cm ptr kind size align
  exact cm_deallocate_bm_eq cm ptr kind size align

private theorem evalPrintM_bm_eq :
    ∀ (stream : DynWrite) (args : List (Val × Gen.«Type»)),
      evalPrintM (M := BM) stream args = evalPrint stream args
  | stream, [] => by unfold evalPrintM evalPrint; rfl
  | stream, (v, _) :: rest => by
    unfold evalPrintM evalPrint
    cases v <;> simp only [evalPrintM_bm_eq]

private theorem evalPrintM_bm_fun : @evalPrintM BM _ = evalPrint := by
  funext stream args
  exact evalPrintM_bm_eq stream args

private theorem loadRawDataM_bm_eq (m : Mach) (ptr : Gen.Pointer Prov) (ptrTy : Gen.PtrType) :
    loadRawDataM (M := BM) m ptr ptrTy = loadRawData m ptr ptrTy := by
  unfold loadRawDataM loadRawData
  rw [abstractByte_dataM_bm_eq]
  rfl

private theorem loadRawDataM_bm_fun : @loadRawDataM BM _ _ = loadRawData := by
  funext m ptr ptrTy
  exact loadRawDataM_bm_eq m ptr ptrTy

private theorem activeThreadM_bm_eq (m : Mach) : activeThreadM (M := BM) m = activeThread m :=
  rfl

private theorem evalIntrinsicM_bm_eq_rawEq (m : Mach) (args : List (Val × Gen.«Type»))
    (retTy : Gen.«Type») :
    evalIntrinsicM (M := BM) m .RawEq args retTy = evalIntrinsic m .RawEq args retTy := by
  simp only [evalIntrinsicM, evalIntrinsic, loadRawDataM_bm_fun]
  rcases args with _ | ⟨⟨lV, lT⟩, _ | ⟨⟨rV, rT⟩, _ | ⟨_, _⟩⟩⟩ <;> try rfl
  cases retTy with
  | Bool =>
    dsimp only
    by_cases hte : typeEq lT rT = true
    · simp only [hte, Bool.not_true]
      rcases lV with _ | _ | lp | _ | _ <;> try rfl
      rcases rV with _ | _ | rp | _ | _ <;> try rfl
    · simp only [Bool.not_eq_true] at hte
      simp only [hte, Bool.not_false]
      rfl
  | _ => rfl

private theorem evalIntrinsicM_bm_eq_allocate (m : Mach) (args : List (Val × Gen.«Type»))
    (retTy : Gen.«Type») :
    evalIntrinsicM (M := BM) m .Allocate args retTy = evalIntrinsic m .Allocate args retTy := by
  simp only [evalIntrinsicM, evalIntrinsic, cm_allocate_bm_fun]
  rcases args with _ | ⟨⟨sizeV, sT⟩, _ | ⟨⟨alignV, aT⟩, _ | ⟨_, _⟩⟩⟩ <;> try rfl
  cases sizeV with
  | Int size =>
    rcases hs : sizeFromBytes size with _ | sz <;> simp only [hs]
    cases alignV with
    | Int align =>
      rcases ha : alignFromBytesInt align with _ | al <;> simp only [ha]
      cases retTy with
      | Ptr retPtrTy => by_cases hk : PtrType.meta_kind retPtrTy = .None <;> simp [hk] <;> rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

private theorem evalIntrinsicM_bm_eq_deallocate (m : Mach) (args : List (Val × Gen.«Type»))
    (retTy : Gen.«Type») :
    evalIntrinsicM (M := BM) m .Deallocate args retTy =
      evalIntrinsic m .Deallocate args retTy := by
  simp only [evalIntrinsicM, evalIntrinsic, cm_deallocate_bm_fun]
  rcases args with _ | ⟨⟨ptrV, pT⟩, _ | ⟨⟨sizeV, sT⟩, _ | ⟨⟨alignV, aT⟩, _ | ⟨_, _⟩⟩⟩⟩ <;>
    try rfl
  rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ <;> try rfl
  cases sizeV with
  | Int size =>
    rcases hs : sizeFromBytes size with _ | sz <;> simp only [hs]
    cases alignV with
    | Int align =>
      rcases ha : alignFromBytesInt align with _ | al <;> simp only [ha]
      split <;> rfl
    | _ => rfl
  | _ => rfl

private theorem evalIntrinsicM_bm_eq_assume (m : Mach) (args : List (Val × Gen.«Type»))
    (retTy : Gen.«Type») :
    evalIntrinsicM (M := BM) m .Assume args retTy = evalIntrinsic m .Assume args retTy := by
  simp only [evalIntrinsicM, evalIntrinsic]
  rcases args with _ | ⟨⟨v, vT⟩, _ | ⟨_, _⟩⟩ <;> try rfl
  cases v with
  | Bool b =>
    dsimp only
    split <;> rfl
  | _ => rfl

private theorem evalIntrinsicM_bm_eq_getUnwindPayload (m : Mach)
    (args : List (Val × Gen.«Type»)) (retTy : Gen.«Type») :
    evalIntrinsicM (M := BM) m .GetUnwindPayload args retTy =
      evalIntrinsic m .GetUnwindPayload args retTy := by
  simp only [evalIntrinsicM, evalIntrinsic]
  split
  · rfl
  · cases retTy with
    | Ptr retPtrTy =>
      by_cases hk : PtrType.meta_kind retPtrTy = .None
      · simp only [hk, ite_true, activeThreadM_bm_eq]
        congr 1
        funext t
        rcases h : t.unwind_payloads.getLast? with _ | tp <;> rfl
      · simp [hk]
    | _ => rfl

private theorem exposeM_bm_eq (ipc : Gen.IntPtrCast Prov) (ptr : Ptr) :
    IntPtrCast.exposeM ipc ptr = IntPtrCast.expose ipc ptr := by
  unfold IntPtrCast.exposeM IntPtrCast.expose
  cases ptr.provenance <;> rfl

private theorem int2ptrProvenanceM_bm_eq (m : Mach) (addr : Int) :
    int2ptrProvenanceM (M := BM) m addr = int2ptrProvenance m addr := by
  unfold int2ptrProvenanceM int2ptrProvenance
  rcases m.intptrcast.exposed.elems with _ | ⟨_, _ | _⟩
  · rfl
  · rfl
  · dsimp only [MemoryOps.exposedInBounds, instMemoryOpsBM]
    rcases int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr with _ | ⟨_, _ | _⟩ <;> rfl

private theorem int2ptrM_bm_eq (m : Mach) (addr : Int) :
    IntPtrCast.int2ptrM (M := BM) m addr = IntPtrCast.int2ptr m addr := by
  unfold IntPtrCast.int2ptrM IntPtrCast.int2ptr
  rw [int2ptrProvenanceM_bm_eq]
  cases int2ptrProvenance m addr <;> rfl

private theorem evalIntrinsicM_bm_eq (m : Mach) (intrinsic : Gen.IntrinsicOp)
    (arguments : List (Val × Gen.«Type»)) (retTy : Gen.«Type») :
    evalIntrinsicM (M := BM) m intrinsic arguments retTy =
      evalIntrinsic m intrinsic arguments retTy := by
  unfold evalIntrinsicM evalIntrinsic
  cases intrinsic with
  | PointerExposeProvenance =>
    dsimp only
    split
    · rfl
    · rename_i hlen
      rcases arguments with _ | ⟨⟨v, _⟩, _ | ⟨_, _⟩⟩
      · simp at hlen
      · cases v with
        | Ptr p =>
          rcases p with ⟨ptr, _ | _⟩
          · cases retTy with
            | Int it =>
              rcases it with ⟨_ | _, ⟨sz⟩⟩
              · by_cases hsz : sz = 8
                · subst hsz; dsimp only; rw [exposeM_bm_eq]
                · simp [hsz]
              · rfl
            | _ => rfl
          · rfl
        | _ => rfl
      · simp at hlen
  | PointerWithExposedProvenance =>
    dsimp only
    split
    · rfl
    · rename_i hlen
      rcases arguments with _ | ⟨⟨v, _⟩, _ | ⟨_, _⟩⟩
      · simp at hlen
      · cases v with
        | Int addr =>
          cases retTy with
          | Ptr retPtrTy =>
            dsimp only
            split
            · rfl
            · exact bind_congr (int2ptrM_bm_eq m addr) (fun _ => rfl)
          | _ => rfl
        | _ => rfl
      · simp at hlen
  | PrintStdout =>
    simp only [evalPrintM_bm_fun]
    split <;> rfl
  | PrintStderr =>
    simp only [evalPrintM_bm_fun]
    split <;> rfl
  | RawEq => exact evalIntrinsicM_bm_eq_rawEq m arguments retTy
  | Allocate => exact evalIntrinsicM_bm_eq_allocate m arguments retTy
  | Deallocate => exact evalIntrinsicM_bm_eq_deallocate m arguments retTy
  | Exit => exact machineExitM_bm_eq m
  | Assume => exact evalIntrinsicM_bm_eq_assume m arguments retTy
  | GetUnwindPayload => exact evalIntrinsicM_bm_eq_getUnwindPayload m arguments retTy
  | _ => rfl

private theorem terminateActiveThreadM_bm_eq (m : Mach) :
    terminateActiveThreadM (M := BM) m = terminateActiveThread m := by
  unfold terminateActiveThreadM terminateActiveThread activeThreadM activeThread
  dsimp only
  split
  · rfl
  · refine bind_congr_right _ (fun t => ?_)
    split
    · rfl
    · refine bind_congr_right _ (fun threads => ?_)
      let q : Nat → Bool := fun i =>
        (threads[i]?.map (fun th => decide (th.state = .BlockedOnJoin m.active_thread))).getD false
      conv =>
        lhs
        rw [filter_eq_of_eq (q := q) (by intro i; dsimp only [q]; cases threads[i]? <;> rfl)]
        rw [map_eq_of_eq
          (g := fun p : Gen.Thread BM × Nat =>
            if ((List.range threads.length).filter q).contains p.2 then
              { p.1 with state := .Enabled }
            else p.1)
          (by intro ⟨_, _⟩; rfl)]
      conv =>
        rhs
        rw [filter_eq_of_eq (q := q) (by intro i; dsimp only [q]; cases threads[i]? <;> rfl)]
        rw [map_eq_of_eq
          (g := fun p : Gen.Thread BM × Nat =>
            if ((List.range threads.length).filter q).contains p.2 then
              { p.1 with state := .Enabled }
            else p.1)
          (by intro ⟨_, _⟩; rfl)]

private theorem evalReturnM_bm_eq (m : Mach) :
    evalReturnM (M := BM) m = evalReturn m := by
  unfold evalReturnM evalReturn activeThreadM activeThread
  cases listIndex m.threads m.active_thread "self.threads[self.active_thread]" with
  | error _ => rfl
  | ok t =>
    dsimp only [bind, Except.bind]
    cases t.stack.getLast? with
    | none => rfl
    | some frame =>
      dsimp only [pure, Except.pure, bind, Except.bind]
      cases listSet m.threads m.active_thread { t with stack := t.stack.dropLast } "pop" with
      | error _ => rfl
      | ok threads =>
        dsimp only [bind, Except.bind]
        cases mapIndex frame.func.locals frame.func.ret "frame.func.locals[frame.func.ret]" with
        | error _ => rfl
        | ok calleeTy =>
          dsimp only [bind, Except.bind]
          cases Type.layout calleeTy with
          | error _ => rfl
          | ok lay =>
            dsimp only [bind, Except.bind]
            cases LayoutStrategy.expect_align lay "the return value is a local and thus sized" with
            | error _ => rfl
            | ok align =>
              dsimp only [bind, Except.bind]
              cases mapIndex frame.locals frame.func.ret "frame.locals[frame.func.ret]" with
              | error _ => rfl
              | ok retPtr =>
                dsimp only [bind, Except.bind]
                rw [typedLoadM_bm_eq]
                rcases typedLoad { m with threads := threads } retPtr calleeTy align .None with
                  _ | ⟨retVal, m1⟩
                · rfl
                · dsimp only [bind, Except.bind]
                  rw [deallocAllM_bm_eq]
                  rcases deallocAll frame.locals.entries.length frame m1.mem with _ | ⟨fr2, cm2⟩
                  · rfl
                  · have hend : ConcurrentMemory.end_call (M := BM) cm2 fr2.extra = .ok cm2 := rfl
                    dsimp only [bind, Except.bind]
                    rw [hend]
                    dsimp only
                    cases fr2.stack_pop_action with
                    | BottomOfStack => exact terminateActiveThreadM_bm_eq { m1 with mem := cm2 }
                    | BackToCaller nextBlock _ callerRetPtr =>
                      dsimp only
                      cases listIndex m1.threads m1.active_thread "self.threads[self.active_thread]" with
                      | error _ => rfl
                      | ok t2 =>
                        dsimp only [bind, Except.bind]
                        split
                        · rfl
                        · rw [typedStoreM_bm_eq]
                          cases typedStore { m1 with mem := cm2 } callerRetPtr retVal calleeTy align .None with
                          | error _ => rfl
                          | ok m2 =>
                            dsimp only [bind, Except.bind]
                            cases nextBlock with
                            | none => rfl
                            | some nb => exact jumpToBlockM_bm_eq m2 nb

theorem evalTerminatorM_bm_eq (m : Mach) (term : Gen.Terminator) :
    evalTerminatorM (M := BM) m term = evalTerminator m term := by
  cases term with
  | Goto nb => exact jumpToBlockM_bm_eq m nb
  | Switch value cases fallback =>
    unfold evalTerminatorM Interp.evalTerminator
    refine bind_congr (evalValueM_bm_eq m value) (fun ⟨⟨v, _⟩, m1⟩ => ?_)
    dsimp only
    cases v with
    | Int i => exact jumpToBlockM_bm_eq m1 ((mapGet cases i).getD fallback)
    | _ => rfl
  | Unreachable => rfl
  | Call callee conv arguments retExpr nextBlock unwindBlock =>
    unfold evalTerminatorM Interp.evalTerminator
    refine bind_congr (evalPlaceM_bm_eq m retExpr) (fun ⟨⟨retPlace, retTy⟩, m1⟩ => ?_)
    dsimp only
    refine bind_congr (prepareForInplacePassingM_bm_eq m1 retPlace retTy) (fun m2 => ?_)
    refine bind_congr (evalValueM_bm_eq m2 callee) (fun ⟨⟨calleeVal, _⟩, m3⟩ => ?_)
    dsimp only
    refine bind_congr (fnFromPtrM_bm_eq m3 calleeVal) (fun calleeFn => ?_)
    refine bind_congr (evalArgumentsM_bm_eq m3 arguments) (fun ⟨args, m4⟩ => ?_)
    exact evalCallM_bm_eq m4 calleeFn conv args (retPlace, retTy) nextBlock unwindBlock
  | Return => exact evalReturnM_bm_eq m
  | Intrinsic intrinsic arguments retExpr nextBlock =>
    unfold evalTerminatorM Interp.evalTerminator
    refine bind_congr (evalPlaceM_bm_eq m retExpr) (fun ⟨⟨retPlace, retTy⟩, m1⟩ => ?_)
    dsimp only
    refine bind_congr (evalArgsM_bm_eq m1 arguments) (fun ⟨args, m2⟩ => ?_)
    dsimp only
    refine bind_congr (evalIntrinsicM_bm_eq m2 intrinsic args retTy) (fun ⟨val, m3⟩ => ?_)
    dsimp only
    refine bind_congr (placeStoreM_bm_eq m3 retPlace val retTy) (fun m4 => ?_)
    cases nextBlock with
    | none => rfl
    | some nb => exact jumpToBlockM_bm_eq m4 nb
  | _ => rfl

private theorem pickActiveThreadM_bm_eq (m : Mach) :
    pickActiveThreadM (M := BM) m = pickActiveThread m := by
  unfold pickActiveThreadM pickActiveThread
  let q : Nat → Bool := fun i =>
    (m.threads[i]?.map (fun t => decide (t.state = .Enabled))).getD false
  conv =>
    lhs
    rw [filter_eq_of_eq (q := q) (by intro i; dsimp only [q]; cases m.threads[i]? <;> rfl)]
  conv =>
    rhs
    rw [filter_eq_of_eq (q := q) (by intro i; dsimp only [q]; cases m.threads[i]? <;> rfl)]

/-- Unconditional single-step specialization identity: polymorphic `stepM`
instantiated at `M = BM` (`BasicMemory<x86_64>`) is extensionally identical to
`Interp.step` on every machine state `m : Mach`. -/
theorem stepM_bm_eq (m : Mach) : stepM (M := BM) m = step m := by
  unfold stepM step
  split
  · rfl
  · have hrst : resetDataRaceTrackingM (M := BM) m = resetDataRaceTracking m := rfl
    rcases hrst_val : resetDataRaceTracking m with ⟨prev, m1⟩
    rw [hrst, hrst_val]
    dsimp only
    rw [pickActiveThreadM_bm_eq]
    cases pickActiveThread m1 with
    | error _ => rfl
    | ok tid =>
      dsimp only [bind, Except.bind]
      rw [curFrameM_bm_eq]
      cases curFrame { m1 with active_thread := tid } with
      | error _ => rfl
      | ok frame =>
        dsimp only [bind, Except.bind]
        cases mapIndex frame.func.blocks frame.next_block "frame.func.blocks[frame.next_block]" with
        | error _ => rfl
        | ok block =>
          dsimp only [bind, Except.bind]
          split
          · rw [evalTerminatorM_bm_eq]
            cases evalTerminator { m1 with active_thread := tid } block.terminator with
            | error _ => rfl
            | ok m2 =>
              dsimp only [bind, Except.bind]
              rw [cm_check_data_races_bm_eq]
          · cases listIndex block.statements frame.next_stmt "block.statements[frame.next_stmt]" with
            | error _ => rfl
            | ok stmt =>
              dsimp only [bind, Except.bind]
              rw [evalStatementM_bm_eq]
              cases evalStatement { m1 with active_thread := tid } stmt with
              | error _ => rfl
              | ok m2 =>
                dsimp only [bind, Except.bind]
                rw [mutateCurFrameM_bm_eq]
                cases mutateCurFrame m2 (fun fr => { fr with next_stmt := fr.next_stmt + 1 }) with
                | error _ => rfl
                | ok m3 =>
                  dsimp only [bind, Except.bind]
                  rw [cm_check_data_races_bm_eq]

/-- Unconditional `n`-step specialization identity: polymorphic `stepsM`
instantiated at `M = BM` equals `Interp.steps` for every `n : Nat` and `m : Mach`,
immediately lifting every `BasicMemory` correspondence theorem (`mirCall_ret`,
`mirCall_ub`, `mirCall_noUB`, `mirCall_progress_N`, `mirCall_steps_error`,
`mirCall_outcome_N`) to `stepsM (M := BM)`. -/
theorem stepsM_bm_eq : ∀ (n : Nat) (m : Mach), stepsM (M := BM) n m = steps n m
  | 0, _ => rfl
  | n + 1, m => by
    simp only [stepsM, steps, stepM_bm_eq m]
    cases step m with
    | error _ => rfl
    | ok m' => exact stepsM_bm_eq n m'


/-! ## Tree Borrows structural invariants and panic-freedom (`spec/mem/tree_borrows/*`) -/

mutual

/-- Structural well-formedness of a `TreeBorrows` borrow-tree node for an
allocation of `sz` bytes: its per-byte `permissions` list has length `sz`,
every byte permission matches the node's `protected` state
(`Permission.matches_protector`), and all child nodes are recursively
well-formed at the same allocation byte length `sz`. -/
def Node.wf (sz : Nat) : Gen.Node → Prop
  | ⟨children, permissions, prot⟩ =>
    permissions.length = sz ∧
    (∀ p ∈ permissions, Permission.matches_protector p prot = true) ∧
    Node.childrenWf sz children

/-- Pointwise `Node.wf sz` across a child-node list. -/
def Node.childrenWf (sz : Nat) : List Gen.Node → Prop
  | [] => True
  | c :: cs => Node.wf sz c ∧ Node.childrenWf sz cs

end

/-- Every allocation in `tbm` (live or dead) has a well-formed borrow tree
whose byte-permission vectors match `(Allocation.size alloc).bytes`. -/
def TreeBorrowsMemory.wf (tbm : Gen.TreeBorrowsMemory Gen.x86_64) : Prop :=
  ∀ alloc ∈ tbm.mem.allocations, Node.wf (Allocation.size alloc).bytes alloc.extra.root

/-- Every **live** allocation in `tbm` has a well-formed borrow tree whose
byte-permission vectors match `(Allocation.size alloc).bytes`. (`release_protector`
and `end_call` preserve `wfLive` even when a weakly protected `Box<T>` was
deallocated before function return.) -/
def TreeBorrowsMemory.wfLive (tbm : Gen.TreeBorrowsMemory Gen.x86_64) : Prop :=
  ∀ alloc ∈ tbm.mem.allocations, alloc.live = true →
    Node.wf (Allocation.size alloc).bytes alloc.extra.root

theorem TreeBorrowsMemory.wfLive_of_wf {tbm : Gen.TreeBorrowsMemory Gen.x86_64}
    (h : TreeBorrowsMemory.wf tbm) : TreeBorrowsMemory.wfLive tbm :=
  fun alloc hm _ => h alloc hm

private theorem bind_ok {α β : Type} {m : Interp α} {f : α → Interp β} {y : β}
    (h : (m >>= f) = .ok y) : ∃ x, m = .ok x ∧ f x = .ok y := by
  cases m with
  | error _ => cases h
  | ok x => exact ⟨x, rfl, h⟩

private theorem interp_pure_ok {α : Type} {x y : α}
    (h : (pure x : Interp α) = .ok y) : x = y := by
  cases h
  rfl

private theorem bind_err {α β : Type} {m : Interp α} {f : α → Interp β} {e : Stop}
    (h : (m >>= f) = .error e) : m = .error e ∨ ∃ x, m = .ok x ∧ f x = .error e := by
  cases m with
  | error _ => cases h; exact .inl rfl
  | ok x => exact .inr ⟨x, rfl, h⟩

private theorem mem_set_or {T : Type} : ∀ {xs : List T} {k : Nat} {x y : T},
    y ∈ xs.set k x → y = x ∨ y ∈ xs
  | [], _, _, _, hy => False.elim (List.not_mem_nil hy)
  | _ :: _, 0, _, _, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inl rfl
    · exact .inr (List.mem_cons_of_mem _ hy)
  | _ :: _, _ + 1, _, _, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inr (List.mem_cons_self ..)
    · rcases mem_set_or hy with rfl | hy'
      · exact .inl rfl
      · exact .inr (List.mem_cons_of_mem _ hy')

private theorem mem_take_sub {T : Type} : ∀ {n : Nat} {xs : List T} {y : T},
    y ∈ xs.take n → y ∈ xs
  | 0, _, _, hy => False.elim (List.not_mem_nil hy)
  | _ + 1, [], _, hy => False.elim (List.not_mem_nil hy)
  | _ + 1, _ :: _, _, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_take_sub hy)

private theorem mem_drop_sub {T : Type} : ∀ {n : Nat} {xs : List T} {y : T},
    y ∈ xs.drop n → y ∈ xs
  | 0, _, _, hy => hy
  | _ + 1, [], _, hy => False.elim (List.not_mem_nil hy)
  | _ + 1, _ :: _, _, hy => List.mem_cons_of_mem _ (mem_drop_sub hy)

private theorem listIndex_ok {T : Type} {xs : List T} {i : Int} {what : String} {x : T}
    (h : listIndex xs i what = .ok x) :
    0 ≤ i ∧ i.toNat < xs.length ∧ xs[i.toNat]? = some x := by
  unfold listIndex at h
  split at h
  · rename_i hge
    generalize hget : xs[i.toNat]? = opt at h
    cases opt with
    | none => cases h
    | some elem =>
      dsimp only at h
      obtain rfl := interp_pure_ok h
      exact ⟨hge, (List.getElem?_eq_some_iff.mp hget).1, rfl⟩
  · cases h

private theorem listSet_ok {T : Type} {xs : List T} {i : Int} {x : T} {what : String}
    {xs' : List T} (h : listSet xs i x what = .ok xs') :
    0 ≤ i ∧ i.toNat < xs.length ∧ xs' = xs.set i.toNat x := by
  unfold listSet at h
  split at h
  · rename_i hb
    exact ⟨hb.1, hb.2, (interp_pure_ok h).symm⟩
  · cases h

private theorem listMutateAt_ok {T O : Type} {xs : List T} {i : Int} {what : String}
    {f : T → Interp (O × T)} {out : O} {xs' : List T}
    (h : listMutateAt xs i what f = .ok (out, xs')) :
    ∃ elem elem', 0 ≤ i ∧ i.toNat < xs.length ∧ xs[i.toNat]? = some elem ∧
      f elem = .ok (out, elem') ∧ xs' = xs.set i.toNat elem' := by
  unfold listMutateAt at h
  obtain ⟨elem, hidx, h⟩ := bind_ok h
  obtain ⟨⟨o, elem'⟩, hf, h⟩ := bind_ok h
  obtain ⟨ys, hset, h⟩ := bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  obtain ⟨hge, hlt, hget⟩ := listIndex_ok hidx
  obtain ⟨_, _, rfl⟩ := listSet_ok hset
  exact ⟨elem, elem', hge, hlt, hget, hf, rfl⟩

private theorem writeSubsliceAtIndex_ok {T : Type} {xs : List T} {start : Int} {src ys : List T}
    (h : writeSubsliceAtIndex xs start src = .ok ys) :
    0 ≤ start ∧ start + src.length ≤ xs.length ∧
      ys.length = xs.length ∧ (∀ y ∈ ys, y ∈ xs ∨ y ∈ src) := by
  unfold writeSubsliceAtIndex at h
  split at h
  · rename_i hb
    obtain rfl := interp_pure_ok h
    refine ⟨hb.1, hb.2, ?_, fun y hy => ?_⟩
    · simp only [List.length_append, List.length_take, List.length_drop]
      omega
    · simp only [List.mem_append] at hy
      rcases hy with (hy | hy) | hy
      · exact .inl (mem_take_sub hy)
      · exact .inr hy
      · exact .inl (mem_drop_sub hy)
  · cases h

private theorem list_mapM_loop_ok {α β : Type} {f : α → Interp β} {P : β → Prop}
    (hf : ∀ x y, f x = .ok y → P y) :
    ∀ (xs : List α) (acc ys : List β),
      List.mapM.loop f xs acc = .ok ys →
      (∀ y ∈ acc, P y) →
      ys.length = acc.length + xs.length ∧ ∀ y ∈ ys, P y
  | [], acc, ys, h, hacc => by
    unfold List.mapM.loop at h
    obtain rfl := interp_pure_ok h
    exact ⟨by simp, fun y hy => hacc y (List.mem_reverse.mp hy)⟩
  | x :: xs, acc, ys, h, hacc => by
    unfold List.mapM.loop at h
    obtain ⟨b, hfx, h⟩ := bind_ok h
    obtain ⟨hlen, hP⟩ := list_mapM_loop_ok hf xs (b :: acc) ys h fun y hy => by
      rcases List.mem_cons.mp hy with hy_eq | hy
      · rw [hy_eq]
        exact hf x b hfx
      · exact hacc y hy
    exact ⟨by simp only [List.length_cons] at hlen ⊢; omega, hP⟩

/-- `Permission.transition` never raises `Stop.specPanic` (every failure is
well-typed Tree Borrows UB). -/
theorem Permission.transition_no_specPanic (p : Gen.Permission) (ak : Gen.AccessKind)
    (nr : Gen.NodeRelation) (msg : String) :
    Permission.transition p ak nr ≠ .error (.specPanic msg) := by
  cases p with
  | Unprot u =>
    cases nr <;> cases ak <;> cases u <;>
      simp [Permission.transition, PermissionUnprot.transition,
        PermissionUnprot.local_read, PermissionUnprot.local_write,
        PermissionUnprot.foreign_read, PermissionUnprot.foreign_write,
        pure, Except.pure, bind, Except.bind, ub]
  | Prot q =>
    cases nr <;> cases ak <;> cases q <;>
      repeat (first
        | simp [Permission.transition, PermissionProt.transition,
            PermissionProt.local_read, PermissionProt.local_write,
            PermissionProt.foreign_read, PermissionProt.foreign_write,
            pure, Except.pure, bind, Except.bind, ub]
        | (rename_i b; cases b))

/-- `Node.transitionRange` preserves permission-list byte length and
`Permission.matches_protector`. -/
theorem Node.transitionRange_wf (nr : Gen.NodeRelation) (ak : Gen.AccessKind)
    (prot : Gen.Protected) :
    ∀ (rem offset : Nat) (perms perms' : List Gen.Permission),
      (∀ p ∈ perms, Permission.matches_protector p prot = true) →
      Node.transitionRange nr ak offset rem perms = .ok perms' →
      perms'.length = perms.length ∧
      ∀ p ∈ perms', Permission.matches_protector p prot = true
  | 0, _, perms, perms', hmp, h => by
    unfold Node.transitionRange at h
    obtain rfl := interp_pure_ok h
    exact ⟨rfl, hmp⟩
  | rem + 1, offset, perms, perms', hmp, h => by
    unfold Node.transitionRange at h
    obtain ⟨⟨_, mid⟩, hm, h⟩ := bind_ok h
    obtain ⟨elem, elem', _, _, hget, hf, rfl⟩ := listMutateAt_ok hm
    obtain ⟨p', htr, hf⟩ := bind_ok hf
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hf)
    have helem : Permission.matches_protector p' prot = true :=
      Permission.transition_preserves_matches_protector
        (hmp elem (List.mem_of_getElem? hget)) htr
    have hmid : ∀ p ∈ perms.set (Int.ofNat offset).toNat p',
        Permission.matches_protector p prot = true := by
      intro p hp
      rcases mem_set_or hp with rfl | hp'
      · exact helem
      · exact hmp p hp'
    obtain ⟨hlen, hmp'⟩ := Node.transitionRange_wf nr ak prot rem (offset + 1) _ perms' hmid h
    exact ⟨hlen.trans (List.length_set ..), hmp'⟩

/-- In-bounds `Node.transitionRange` (`offset + rem ≤ perms.length`) never
raises `Stop.specPanic`. -/
theorem Node.transitionRange_no_specPanic (nr : Gen.NodeRelation) (ak : Gen.AccessKind)
    (msg : String) :
    ∀ (rem offset : Nat) (perms : List Gen.Permission),
      offset + rem ≤ perms.length →
      Node.transitionRange nr ak offset rem perms ≠ .error (.specPanic msg)
  | 0, _, _, _, h => by
    unfold Node.transitionRange at h
    cases h
  | rem + 1, offset, perms, hle, h => by
    unfold Node.transitionRange at h
    have hlt : offset < perms.length := by omega
    rcases bind_err h with hm | ⟨⟨_, mid⟩, hm, h⟩
    · unfold listMutateAt at hm
      obtain ⟨elem, hget⟩ : ∃ e, perms[offset]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
      have hidx : listIndex perms (Int.ofNat offset) "Node::transition" = .ok elem := by
        simp [listIndex, hget, pure, Except.pure]
      rcases bind_err hm with hidx_err | ⟨elem0, hidx0, hm⟩
      · rw [hidx] at hidx_err; cases hidx_err
      · rw [hidx] at hidx0; obtain rfl := Except.ok.inj hidx0
        rcases bind_err hm with hf_err | ⟨⟨_, elem'⟩, _, hset_err⟩
        · rcases bind_err hf_err with htr_err | ⟨_, _, hpure_err⟩
          · exact Permission.transition_no_specPanic elem ak nr msg htr_err
          · cases hpure_err
        · rcases bind_err hset_err with hs_err | ⟨_, _, hpure_err⟩
          · have hset_ok : listSet perms (Int.ofNat offset) elem' "Node::transition" =
                .ok (perms.set offset elem') := by
              simp [listSet, hlt, pure, Except.pure]
            rw [hset_ok] at hs_err; cases hs_err
          · cases hpure_err
    · obtain ⟨_, elem', _, _, _, _, rfl⟩ := listMutateAt_ok hm
      exact Node.transitionRange_no_specPanic nr ak msg rem (offset + 1)
        (perms.set (Int.ofNat offset).toNat elem') (by rw [List.length_set]; omega) h

/-- `Node.transition` preserves `Node.wf sz` (keeping child subtrees intact). -/
theorem Node.transition_wf {sz : Nat} {n n' : Gen.Node} {nr : Gen.NodeRelation}
    {ak : Gen.AccessKind} {offset : Gen.Offset} {size : Size}
    (hwf : Node.wf sz n) (h : Node.transition n nr ak offset size = .ok n') :
    Node.wf sz n' := by
  rcases n with ⟨children, perms, prot⟩
  obtain ⟨hlen, hmp, hch⟩ := hwf
  unfold Node.transition at h
  obtain ⟨perms', htr, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  obtain ⟨hlen', hmp'⟩ :=
    Node.transitionRange_wf nr ak prot size.bytes offset.bytes perms perms' hmp htr
  exact ⟨hlen'.trans hlen, hmp', hch⟩

mutual

/-- `Node.access` preserves `Node.wf sz` across the entire borrow tree. -/
theorem Node.access_wf {sz : Nat} :
    ∀ {n n' : Gen.Node} {path : Option Gen.Path} {ak : Gen.AccessKind}
      {offset : Gen.Offset} {size : Size},
      Node.wf sz n → Node.access n path ak offset size = .ok n' → Node.wf sz n'
  | ⟨children, permissions, prot⟩, n', path, ak, offset, size, hwf, h => by
    unfold Node.access at h
    obtain ⟨self1, htr, h⟩ := bind_ok h
    obtain ⟨children', hch, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    have hwf1 := Node.transition_wf hwf htr
    rcases self1 with ⟨_, perms1, prot1⟩
    exact ⟨hwf1.1, hwf1.2.1, Node.accessChildren_wf hwf.2.2 hch⟩

/-- `Node.accessChildren` preserves `Node.childrenWf sz`. -/
theorem Node.accessChildren_wf {sz : Nat} :
    ∀ {cs cs' : List Gen.Node} {childId : Int} {path : Option Gen.Path}
      {ak : Gen.AccessKind} {offset : Gen.Offset} {size : Size},
      Node.childrenWf sz cs →
      Node.accessChildren childId path ak offset size cs = .ok cs' →
      Node.childrenWf sz cs'
  | [], cs', _, _, _, _, _, _, h => by
    unfold Node.accessChildren at h
    obtain rfl := interp_pure_ok h
    trivial
  | c :: cs, cs', childId, path, ak, offset, size, ⟨hc, hcs⟩, h => by
    unfold Node.accessChildren at h
    obtain ⟨c', h1, h⟩ := bind_ok h
    obtain ⟨rest', h2, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    exact ⟨Node.access_wf hc h1, Node.accessChildren_wf hcs h2⟩

end

mutual

/-- On a well-formed node (`Node.wf sz n`), any in-bounds `Node.access`
(`offset.bytes + size.bytes ≤ sz`) never fails with `Stop.specPanic`. -/
theorem Node.access_no_specPanic {sz : Nat} :
    ∀ (n : Gen.Node) (path : Option Gen.Path) (ak : Gen.AccessKind)
      (offset : Gen.Offset) (size : Size) (msg : String),
      Node.wf sz n → offset.bytes + size.bytes ≤ sz →
      Node.access n path ak offset size ≠ .error (.specPanic msg)
  | ⟨children, permissions, prot⟩, path, ak, offset, size, msg, ⟨hlen, _, hch⟩, hle, h => by
    unfold Node.access at h
    rcases bind_err h with htr | ⟨self1, _, h⟩
    · unfold Node.transition at htr
      rcases bind_err htr with hrange | ⟨_, _, hpure⟩
      · exact Node.transitionRange_no_specPanic (if path.isSome then .Local else .Foreign)
          ak msg size.bytes offset.bytes permissions (by omega) hrange
      · cases hpure
    · rcases bind_err h with hcs | ⟨_, _, hpure⟩
      · exact Node.accessChildren_no_specPanic children 0 path ak offset size msg hch hle hcs
      · cases hpure

/-- In-bounds `Node.accessChildren` on well-formed children never raises
`Stop.specPanic`. -/
theorem Node.accessChildren_no_specPanic {sz : Nat} :
    ∀ (cs : List Gen.Node) (childId : Int) (path : Option Gen.Path)
      (ak : Gen.AccessKind) (offset : Gen.Offset) (size : Size) (msg : String),
      Node.childrenWf sz cs → offset.bytes + size.bytes ≤ sz →
      Node.accessChildren childId path ak offset size cs ≠ .error (.specPanic msg)
  | [], _, _, _, _, _, _, _, _, h => by
    unfold Node.accessChildren at h
    cases h
  | c :: cs, childId, path, ak, offset, size, msg, ⟨hc, hcs⟩, hle, h => by
    unfold Node.accessChildren at h
    rcases bind_err h with h1 | ⟨c', _, h⟩
    · exact Node.access_no_specPanic c _ ak offset size msg hc hle h1
    · rcases bind_err h with h2 | ⟨_, _, hpure⟩
      · exact Node.accessChildren_no_specPanic cs (childId + 1) path ak offset size msg hcs hle h2
      · cases hpure

end

/-- When `settings` satisfies `matches_protector settings.outside prot` and
`(∀ p ∈ settings.inside, matches_protector p prot)` (as established by
`ReborrowSettings.new_matches_protector`), splicing `settings.inside` into
`List.replicate allocSize settings.outside` yields a permission list that
satisfies `permissions.all (matches_protector · prot) = true` (proving the
assertion in `TreeBorrowsMemory.reborrow` unreachable for all
`ReborrowSettings.new` outputs). -/
theorem reborrow_childPermissions_matches_protector {s : Gen.ReborrowSettings}
    (hout : Permission.matches_protector s.outside s.«protected» = true)
    (hins : ∀ p ∈ s.inside, Permission.matches_protector p s.«protected» = true)
    (allocSize : Nat) :
    ((List.replicate allocSize s.outside).all
      (fun x => Permission.matches_protector x s.«protected») = true) ∧
    ∀ (offset : Int) (ys : List Gen.Permission),
      writeSubsliceAtIndex (List.replicate allocSize s.outside) offset s.inside = .ok ys →
      ys.all (fun x => Permission.matches_protector x s.«protected») = true := by
  have hrep : ∀ p ∈ List.replicate allocSize s.outside,
      Permission.matches_protector p s.«protected» = true := by
    intro p hp
    rw [List.eq_of_mem_replicate hp]
    exact hout
  refine ⟨List.all_eq_true.mpr hrep, fun offset ys hws => List.all_eq_true.mpr fun p hp => ?_⟩
  rcases (writeSubsliceAtIndex_ok hws).2.2.2 p hp with hp' | hp'
  · exact hrep p hp'
  · exact hins p hp'

/-- `Node.access_node` preserves `Node.wf sz` whenever `f` preserves `Node.wf sz`
at the visited target node. -/
theorem Node.access_node_wf {O : Type} {sz : Nat} {f : Gen.Node → Interp (O × Gen.Node)}
    (hf : ∀ u u' o, Node.wf sz u → f u = .ok (o, u') → Node.wf sz u') :
    ∀ (path : Gen.Path) {n n' : Gen.Node} {out : O},
      Node.wf sz n → Node.access_node f path n = .ok (out, n') → Node.wf sz n'
  | [], n, n', out, hwf, h => hf n n' out hwf h
  | subRootId :: subPath, ⟨children, permissions, prot⟩, n', out, ⟨hlen, hmp, hch⟩, h => by
    unfold Node.access_node at h
    split at h
    · cases h
    · obtain ⟨⟨o, children'⟩, hm, h⟩ := bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
      obtain ⟨elem, elem', _, _, hget, hsub, rfl⟩ := listMutateAt_ok hm
      have hch_mem : ∀ {cs : List Gen.Node}, Node.childrenWf sz cs → ∀ c ∈ cs, Node.wf sz c := by
        intro cs hcs c hc
        induction cs with
        | nil => exact False.elim (List.not_mem_nil hc)
        | cons d ds ih =>
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hcs.1
          · exact ih hcs.2 hc
      have helem' : Node.wf sz elem' :=
        Node.access_node_wf hf subPath (hch_mem hch elem (List.mem_of_getElem? hget)) hsub
      have hch_set : ∀ {cs : List Gen.Node} (k : Nat),
          Node.childrenWf sz cs → Node.childrenWf sz (cs.set k elem') := by
        intro cs k hcs
        induction cs generalizing k with
        | nil => trivial
        | cons d ds ih =>
          cases k with
          | zero => exact ⟨helem', hcs.2⟩
          | succ k => exact ⟨hcs.1, ih k hcs.2⟩
      exact ⟨hlen, hmp, hch_set subRootId.toNat hch⟩

private theorem childrenWf_append_singleton {sz : Nat} {child : Gen.Node}
    (hc : Node.wf sz child) :
    ∀ {cs : List Gen.Node}, Node.childrenWf sz cs → Node.childrenWf sz (cs ++ [child])
  | [], _ => ⟨hc, trivial⟩
  | _ :: _, ⟨hd, hds⟩ => ⟨hd, childrenWf_append_singleton hc hds⟩

/-- `Node.add_node` preserves `Node.wf sz` when both the parent tree and the
appended child node satisfy `Node.wf sz`. -/
theorem Node.add_node_wf {sz : Nat} {root root' child : Gen.Node} {parentPath childPath : Gen.Path}
    (hroot : Node.wf sz root) (hchild : Node.wf sz child)
    (h : Node.add_node root parentPath child = .ok (childPath, root')) :
    Node.wf sz root' := by
  unfold Node.add_node at h
  obtain ⟨⟨idx, r1⟩, hm, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  refine Node.access_node_wf (fun u u' o hu hfu => ?_) parentPath hroot hm
  rcases u with ⟨uch, uperms, uprot⟩
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hfu)
  exact ⟨hu.1, hu.2.1, childrenWf_append_singleton hchild hu.2.2⟩

/-- `TreeBorrowsMemory.reborrowInitAccess` preserves `Node.wf sz`. -/
theorem TreeBorrowsMemory.reborrowInitAccess_wf {sz : Nat} (childPath : Gen.Path)
    (offset : Gen.Offset) :
    ∀ (idx : Nat) (inside : List Gen.Permission) {root root' : Gen.Node},
      Node.wf sz root →
      TreeBorrowsMemory.reborrowInitAccess childPath offset idx inside root = .ok root' →
      Node.wf sz root'
  | _, [], _, _, hwf, h => by
    unfold TreeBorrowsMemory.reborrowInitAccess at h
    obtain rfl := interp_pure_ok h
    exact hwf
  | idx, perm :: rest, root, root', hwf, h => by
    unfold TreeBorrowsMemory.reborrowInitAccess at h
    dsimp only at h
    cases hp : Permission.init_access perm with
    | none =>
      simp only [hp, pure, Except.pure, bind, Except.bind] at h
      exact TreeBorrowsMemory.reborrowInitAccess_wf childPath offset (idx + 1) rest hwf h
    | some access =>
      simp only [hp] at h
      obtain ⟨root1, hstep, h⟩ := bind_ok h
      exact TreeBorrowsMemory.reborrowInitAccess_wf childPath offset (idx + 1) rest
        (Node.access_wf hwf hstep) h

/-- `TreeBorrowsMemory.new` constructs an empty, well-formed Tree Borrows memory. -/
theorem TreeBorrowsMemory.new_wf (params : Gen.TreeBorrowsParams) :
    TreeBorrowsMemory.wf (TreeBorrowsMemory.new params) := by
  intro alloc hm
  exact False.elim (List.not_mem_nil hm)

/-- `TreeBorrowsMemory.allocate` preserves `TreeBorrowsMemory.wf` (initializing a
fresh unprotected `.Unique` root node of byte length `size.bytes`). -/
theorem TreeBorrowsMemory.allocate_wf {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {kind : Gen.AllocationKind} {size : Size} {align : Align}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    (hwf : TreeBorrowsMemory.wf tbm)
    (h : TreeBorrowsMemory.allocate tbm kind size align = .ok (ptr, tbm')) :
    TreeBorrowsMemory.wf tbm' := by
  unfold TreeBorrowsMemory.allocate at h
  obtain ⟨⟨ptr1, mem'⟩, halloc, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  unfold BasicMemory.allocate at halloc
  split at halloc
  · cases halloc
  · cases hpick : BasicMemory.pickAddr tbm.mem size align with
    | none =>
      simp only [hpick] at halloc
      cases halloc
    | some addr =>
      simp only [hpick] at halloc
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok halloc)
      intro alloc hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hwf alloc hm
      · rw [List.mem_singleton.mp hm]
        refine ⟨by simp [Allocation.size], fun p hp => ?_, trivial⟩
        rw [List.eq_of_mem_replicate hp]
        rfl

/-- `TreeBorrowsMemory.load` preserves `TreeBorrowsMemory.wf`. -/
theorem TreeBorrowsMemory.load_wf {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {len : Size} {align : Align}
    {bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)}
    (hwf : TreeBorrowsMemory.wf tbm)
    (h : TreeBorrowsMemory.load tbm ptr len align = .ok (bytes, tbm')) :
    TreeBorrowsMemory.wf tbm' := by
  unfold TreeBorrowsMemory.load at h
  obtain ⟨⟨bs, mem'⟩, hload, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  unfold BasicMemory.load at hload
  split at hload
  · cases hload
  · obtain ⟨opt, hck, hload⟩ := bind_ok hload
    cases opt with
    | none =>
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hload)
      exact hwf
    | some triple =>
      rcases triple with ⟨id, provExtra, offset⟩
      obtain ⟨allocation, hidx, hload⟩ := bind_ok hload
      obtain ⟨extra', hextra, hload⟩ := bind_ok hload
      obtain ⟨allocations', hset, hload⟩ := bind_ok hload
      obtain ⟨_, _, hload⟩ := bind_ok hload
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hload)
      obtain ⟨root', hacc, hextra⟩ := bind_ok hextra
      obtain rfl := interp_pure_ok hextra
      obtain ⟨_, _, rfl⟩ := listSet_ok hset
      obtain ⟨_, _, hget⟩ := listIndex_ok hidx
      intro alloc hm
      rcases mem_set_or hm with rfl | hm'
      · exact Node.access_wf (hwf allocation (List.mem_of_getElem? hget)) hacc
      · exact hwf alloc hm'

/-- `TreeBorrowsMemory.store` preserves `TreeBorrowsMemory.wf` (since
`writeSubsliceAtIndex` preserves `allocation.data.length`). -/
theorem TreeBorrowsMemory.store_wf {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    {bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)} {align : Align}
    (hwf : TreeBorrowsMemory.wf tbm)
    (h : TreeBorrowsMemory.store tbm ptr bytes align = .ok tbm') :
    TreeBorrowsMemory.wf tbm' := by
  unfold TreeBorrowsMemory.store at h
  obtain ⟨mem', hstore, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  unfold BasicMemory.store at hstore
  split at hstore
  · cases hstore
  · obtain ⟨opt, hck, hstore⟩ := bind_ok hstore
    cases opt with
    | none =>
      obtain rfl := interp_pure_ok hstore
      exact hwf
    | some triple =>
      rcases triple with ⟨id, provExtra, offset⟩
      obtain ⟨allocation, hidx, hstore⟩ := bind_ok hstore
      obtain ⟨extra', hextra, hstore⟩ := bind_ok hstore
      obtain ⟨data', hws, hstore⟩ := bind_ok hstore
      obtain ⟨allocations', hset, hstore⟩ := bind_ok hstore
      obtain rfl := interp_pure_ok hstore
      obtain ⟨root', hacc, hextra⟩ := bind_ok hextra
      obtain rfl := interp_pure_ok hextra
      obtain ⟨_, _, rfl⟩ := listSet_ok hset
      obtain ⟨_, _, hget⟩ := listIndex_ok hidx
      have hdata_len := (writeSubsliceAtIndex_ok hws).2.2.1
      intro alloc hm
      rcases mem_set_or hm with rfl | hm'
      · dsimp only [Allocation.size]
        rw [hdata_len]
        exact Node.access_wf (hwf allocation (List.mem_of_getElem? hget)) hacc
      · exact hwf alloc hm'

/-- `TreeBorrowsMemory.deallocate` preserves `TreeBorrowsMemory.wf`. -/
theorem TreeBorrowsMemory.deallocate_wf {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {kind : Gen.AllocationKind}
    {size : Size} {align : Align}
    (hwf : TreeBorrowsMemory.wf tbm)
    (h : TreeBorrowsMemory.deallocate tbm ptr kind size align = .ok tbm') :
    TreeBorrowsMemory.wf tbm' := by
  unfold TreeBorrowsMemory.deallocate at h
  obtain ⟨mem', hdealloc, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  unfold BasicMemory.deallocate at hdealloc
  cases hprov : ptr.provenance with
  | none =>
    simp only [hprov] at hdealloc
    cases hdealloc
  | some pair =>
    rcases pair with ⟨id, provExtra⟩
    simp only [hprov] at hdealloc
    obtain ⟨allocation, hidx, hdealloc⟩ := bind_ok hdealloc
    split at hdealloc; · cases hdealloc
    split at hdealloc; · cases hdealloc
    split at hdealloc; · dsimp only [ub] at hdealloc; cases hdealloc
    split at hdealloc; · cases hdealloc
    split at hdealloc; · cases hdealloc
    obtain ⟨extra', hextra, hdealloc⟩ := bind_ok hdealloc
    obtain ⟨allocations', hset, hdealloc⟩ := bind_ok hdealloc
    obtain rfl := interp_pure_ok hdealloc
    obtain ⟨root', hacc, hextra⟩ := bind_ok hextra
    split at hextra; · cases hextra
    obtain rfl := interp_pure_ok hextra
    obtain ⟨_, _, rfl⟩ := listSet_ok hset
    obtain ⟨_, _, hget⟩ := listIndex_ok hidx
    intro alloc hm
    rcases mem_set_or hm with rfl | hm'
    · exact Node.access_wf (hwf allocation (List.mem_of_getElem? hget)) hacc
    · exact hwf alloc hm'

/-- `TreeBorrowsMemory.reborrow` unconditionally preserves `TreeBorrowsMemory.wf`
on every `.ok` step (guarded by `writeSubsliceAtIndex` length preservation,
`Permission.matches_protector` validation, `Node.add_node_wf`, and
`reborrowInitAccess_wf`). -/
theorem TreeBorrowsMemory.reborrow_wf {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr ptr' : Gen.ThinPointer Gen.TreeBorrowsProvenance} {settings : Gen.ReborrowSettings}
    {fe fe' : Gen.TreeBorrowsFrameExtra}
    (hwf : TreeBorrowsMemory.wf tbm)
    (h : TreeBorrowsMemory.reborrow tbm ptr settings fe = .ok (ptr', tbm', fe')) :
    TreeBorrowsMemory.wf tbm' := by
  unfold TreeBorrowsMemory.reborrow at h
  dsimp only at h
  obtain ⟨_, hck, h⟩ := bind_ok h
  cases hprov : ptr.provenance with
  | none =>
    simp only [hprov] at h
    split at h
    · cases h
    · obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
      obtain ⟨rfl, _⟩ := Prod.mk.inj h
      exact hwf
  | some pair =>
    rcases pair with ⟨allocId, parentPath⟩
    simp only [hprov] at h
    obtain ⟨⟨childPath, allocations'⟩, hm, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    obtain ⟨allocation, alloc', _, _, hget, hf, rfl⟩ := listMutateAt_ok hm
    cases hoff : Size.from_bytes (ptr.addr - allocation.addr) with
    | none =>
      simp [hoff, specPanic, bind, Except.bind] at hf
    | some offset =>
      simp only [hoff, pure, Except.pure, bind, Except.bind] at hf
      have hbody : ∀ (permissions : List Gen.Permission),
          permissions.length = (Allocation.size allocation).bytes →
          (let childNode : Gen.Node :=
            { children := [], permissions := permissions, «protected» := settings.«protected» }
           if (!childNode.permissions.all fun x =>
               Permission.matches_protector x childNode.«protected») = true then
             specPanic
               "assertion failed: child_node.permissions.all(|x| x.matches_protector(child_node.protected))"
           else do
             let (cp, root1) ← Node.add_node allocation.extra.root parentPath childNode
             let root2 ← TreeBorrowsMemory.reborrowInitAccess cp offset 0 settings.inside root1
             pure (cp, { data := allocation.data, addr := allocation.addr, align := allocation.align,
                         kind := allocation.kind, live := allocation.live, extra := { root := root2 } })) =
            .ok (childPath, alloc') →
          TreeBorrowsMemory.wf
            { params := tbm.params,
              mem := { allocations := tbm.mem.allocations.set allocId._0.toNat alloc',
                       _phantom := tbm.mem._phantom } } := by
        intro permissions hplen hfb
        dsimp only at hfb
        cases hall : permissions.all (fun x => Permission.matches_protector x settings.«protected») with
        | false =>
          simp only [hall, Bool.not_false, ↓reduceIte] at hfb
          cases hfb
        | true =>
          simp only [hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfb
          obtain ⟨⟨cp, root1⟩, hadd, hfb⟩ := bind_ok hfb
          dsimp only at hfb
          obtain ⟨root2, hinit, hfb⟩ := bind_ok hfb
          obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hfb)
          have hchild_wf : Node.wf (Allocation.size allocation).bytes
              { children := [], permissions := permissions, «protected» := settings.«protected» } :=
            ⟨hplen, List.all_eq_true.mp hall, trivial⟩
          have hr1 := Node.add_node_wf (hwf allocation (List.mem_of_getElem? hget)) hchild_wf hadd
          have hr2 := TreeBorrowsMemory.reborrowInitAccess_wf cp offset 0 settings.inside hr1 hinit
          intro alloc hm'
          rcases mem_set_or hm' with rfl | hm''
          · exact hr2
          · exact hwf alloc hm''
      by_cases hgt : settings.inside.length > 0
      · simp only [hgt, ↓reduceIte] at hf
        obtain ⟨permissions, hps, hf⟩ := bind_ok hf
        exact hbody permissions ((writeSubsliceAtIndex_ok hps).2.2.1.trans (List.length_replicate ..)) hf
      · simp only [hgt, ↓reduceIte] at hf
        exact hbody _ (List.length_replicate ..) hf

/-- `TreeBorrowsMemory.retag_ptr` preserves `TreeBorrowsMemory.wf`. -/
theorem TreeBorrowsMemory.retag_ptr_wf {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {fe fe' : Gen.TreeBorrowsFrameExtra} {ptr ptr' : Gen.Pointer Gen.TreeBorrowsProvenance}
    {ptrType : Gen.PtrType} {fnEntry fnImplicitWrites : Bool}
    {vtableLookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable}
    (hwf : TreeBorrowsMemory.wf tbm)
    (h : TreeBorrowsMemory.retag_ptr tbm fe ptr ptrType fnEntry fnImplicitWrites vtableLookup =
      .ok (ptr', tbm', fe')) :
    TreeBorrowsMemory.wf tbm' := by
  unfold TreeBorrowsMemory.retag_ptr at h
  obtain ⟨opt, hs, h⟩ := bind_ok h
  cases opt with
  | none =>
    obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    exact hwf
  | some perms =>
    obtain ⟨⟨thin', tbm1, fe1⟩, hreb, h⟩ := bind_ok h
    obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    exact TreeBorrowsMemory.reborrow_wf hwf hreb

/-- Non-ZST relative-offset and slice-bounds safety of `BasicMemory.check_ptr`
inside `TreeBorrowsMemory.reborrow`: whenever `settings.inside.length > 0`
(a non-zero-sized pointee), `BasicMemory.check_ptr` guarantees that
`ptr.addr - allocation.addr ≥ 0` (so `Size.from_bytes` returns `some offset` and
`Offset::from_bytes(...).unwrap()` cannot panic!) AND
`offset.bytes + settings.inside.length ≤ (Allocation.size allocation).bytes`
(so `writeSubsliceAtIndex` cannot panic either!). By contrast, for a ZST
reference (`settings.inside = []`), `BasicMemory.check_ptr` returns `Ok(None)`
immediately without checking `ptr.addr ≥ allocation.addr`, allowing
`Offset::from_bytes(ptr.addr - allocation.addr).unwrap()` to hit `Stop.specPanic`
on negative-offset `wrapping_offset` pointers (exhibited in `TbWitness.lean`). -/
theorem TreeBorrowsMemory.reborrow_nonzst_no_offset_panic
    {tbm : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    {allocId : Gen.AllocId} {parentPath : Gen.Path}
    {settings : Gen.ReborrowSettings}
    {opt : Option (Gen.AllocId × Gen.Path × Size)}
    (hpos : settings.inside.length > 0)
    (hprov : ptr.provenance = some (allocId, parentPath))
    (hck : BasicMemory.check_ptr tbm.mem ptr ⟨settings.inside.length⟩ = .ok opt) :
    ∃ (allocation : _) (offset : Size),
      listIndex tbm.mem.allocations allocId._0 "TreeBorrowsMemory::reborrow" = .ok allocation ∧
      allocation.live = true ∧
      Size.from_bytes (ptr.addr - allocation.addr) = some offset ∧
      offset.bytes + settings.inside.length ≤ (Allocation.size allocation).bytes := by
  unfold BasicMemory.check_ptr at hck
  have hnz : ¬(⟨settings.inside.length⟩ : Size).bytes = 0 := by dsimp; omega
  simp only [hnz, ↓reduceIte, hprov] at hck
  obtain ⟨allocation, hidx, hck⟩ := bind_ok hck
  obtain ⟨hge, _, hget⟩ := listIndex_ok hidx
  have hidx2 : listIndex tbm.mem.allocations allocId._0 "TreeBorrowsMemory::reborrow" =
      .ok allocation := by
    simp [listIndex, hge, hget, pure, Except.pure]
  cases hlive : allocation.live with
  | false =>
    simp only [hlive, Bool.not_false, ↓reduceIte] at hck
    cases hck
  | true =>
    simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hck
    split at hck
    · cases hck
    · rename_i hbounds
      have hoff_nn : (0 : Int) ≤ ptr.addr - allocation.addr :=
        Int.not_lt.mp fun h => hbounds (.inl h)
      have h2 : ¬(ptr.addr - allocation.addr + (settings.inside.length : Int) >
          ((Allocation.size allocation).bytes : Int)) := fun h => hbounds (.inr h)
      refine ⟨allocation, ⟨(ptr.addr - allocation.addr).toNat⟩, hidx2, hlive, ?_, ?_⟩
      · unfold Size.from_bytes
        simp only [hoff_nn, ↓reduceIte]
      · change (ptr.addr - allocation.addr).toNat + settings.inside.length ≤
            (Allocation.size allocation).bytes
        omega

mutual

/-- Intermediate borrow-tree invariant after Step 1 of
`TreeBorrowsMemory.release_protector`: the node at `path` has already had its
`permissions` mapped through `Permission.unprotect` (so they have length `sz` and
match `.No`), while every other node in the tree satisfies `Node.wf sz`. -/
def Node.wfUnprotAt (sz : Nat) : Gen.Path → Gen.Node → Prop
  | [], ⟨children, permissions, _⟩ =>
    permissions.length = sz ∧
    (∀ p ∈ permissions, Permission.matches_protector p .No = true) ∧
    Node.childrenWf sz children
  | idx :: rest, ⟨children, permissions, prot⟩ =>
    permissions.length = sz ∧
    (∀ p ∈ permissions, Permission.matches_protector p prot = true) ∧
    Node.childrenWfUnprotAt sz idx rest 0 children

/-- Child-list invariant locating the unique child `target` along `idx :: rest`. -/
def Node.childrenWfUnprotAt (sz : Nat) (target : Int) (rest : Gen.Path) :
    Nat → List Gen.Node → Prop
  | _, [] => False
  | cur, c :: cs =>
    (target = Int.ofNat cur ∧ Node.wfUnprotAt sz rest c ∧ Node.childrenWf sz cs) ∨
    (target ≠ Int.ofNat cur ∧ Node.wf sz c ∧ Node.childrenWfUnprotAt sz target rest (cur + 1) cs)

end

/-- `Node.releaseProtectorPermissions` preserves byte length and
`Permission.matches_protector`. -/
theorem Node.releaseProtectorPermissions_wf (nr : Gen.NodeRelation) (prot : Gen.Protected) :
    ∀ (accesses : List (Option Gen.AccessKind)) (offset : Nat)
      (perms perms' : List Gen.Permission),
      (∀ p ∈ perms, Permission.matches_protector p prot = true) →
      Node.releaseProtectorPermissions nr offset accesses perms = .ok perms' →
      perms'.length = perms.length ∧
      ∀ p ∈ perms', Permission.matches_protector p prot = true
  | [], _, perms, perms', hmp, h => by
    unfold Node.releaseProtectorPermissions at h
    obtain rfl := interp_pure_ok h
    exact ⟨rfl, hmp⟩
  | none :: rest, offset, perms, perms', hmp, h =>
    Node.releaseProtectorPermissions_wf nr prot rest (offset + 1) perms perms' hmp h
  | some access :: rest, offset, perms, perms', hmp, h => by
    unfold Node.releaseProtectorPermissions at h
    obtain ⟨⟨_, mid⟩, hm, h⟩ := bind_ok h
    obtain ⟨elem, elem', _, _, hget, hf, rfl⟩ := listMutateAt_ok hm
    obtain ⟨p', htr, hf⟩ := bind_ok hf
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hf)
    have helem : Permission.matches_protector p' prot = true :=
      Permission.transition_preserves_matches_protector
        (hmp elem (List.mem_of_getElem? hget)) htr
    have hmid : ∀ p ∈ perms.set (Int.ofNat offset).toNat p',
        Permission.matches_protector p prot = true := by
      intro p hp
      rcases mem_set_or hp with rfl | hp'
      · exact helem
      · exact hmp p hp'
    obtain ⟨hlen, hmp'⟩ :=
      Node.releaseProtectorPermissions_wf nr prot rest (offset + 1) _ perms' hmid h
    exact ⟨hlen.trans (List.length_set ..), hmp'⟩

mutual

/-- Foreign (`path = none`) `Node.release_protector` preserves `Node.wf sz`. -/
theorem Node.release_protector_none_wf {sz : Nat} :
    ∀ {n n' : Gen.Node} {accesses : List (Option Gen.AccessKind)},
      Node.wf sz n → Node.release_protector n none accesses = .ok n' → Node.wf sz n'
  | ⟨children, permissions, prot⟩, n', accesses, ⟨hlen, hmp, hch⟩, h => by
    unfold Node.release_protector at h
    obtain ⟨perms', hp, h⟩ := bind_ok h
    obtain ⟨children', hcs, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    obtain ⟨hlen', hmp'⟩ :=
      Node.releaseProtectorPermissions_wf .Foreign prot accesses 0 permissions perms' hmp hp
    exact ⟨hlen'.trans hlen, hmp', Node.releaseProtectorChildren_none_wf hch hcs⟩

/-- Foreign (`path = none`) `Node.releaseProtectorChildren` preserves
`Node.childrenWf sz`. -/
theorem Node.releaseProtectorChildren_none_wf {sz : Nat} :
    ∀ {cs cs' : List Gen.Node} {childId : Int} {accesses : List (Option Gen.AccessKind)},
      Node.childrenWf sz cs →
      Node.releaseProtectorChildren childId none accesses cs = .ok cs' →
      Node.childrenWf sz cs'
  | [], cs', _, _, _, h => by
    unfold Node.releaseProtectorChildren at h
    obtain rfl := interp_pure_ok h
    trivial
  | c :: cs, cs', childId, accesses, ⟨hc, hcs⟩, h => by
    unfold Node.releaseProtectorChildren at h
    obtain ⟨c', h1, h⟩ := bind_ok h
    obtain ⟨rest', h2, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    exact ⟨Node.release_protector_none_wf hc h1,
      Node.releaseProtectorChildren_none_wf hcs h2⟩

end

private theorem releaseProtectorChildren_gt_wf {sz : Nat} (head : Int) (tail : Gen.Path)
    (accesses : List (Option Gen.AccessKind)) :
    ∀ {cs cs' : List Gen.Node} (childId : Int),
      head < childId → Node.childrenWf sz cs →
      Node.releaseProtectorChildren childId (some (head :: tail)) accesses cs = .ok cs' →
      Node.childrenWf sz cs'
  | [], cs', _, _, _, h => by
    unfold Node.releaseProtectorChildren at h
    obtain rfl := interp_pure_ok h
    trivial
  | c :: cs, cs', childId, hlt, ⟨hc, hcs⟩, h => by
    unfold Node.releaseProtectorChildren at h
    have hne : (head == childId) = false := beq_false_of_ne (by omega)
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨c', h1, h⟩ := bind_ok h
    obtain ⟨rest', h2, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    exact ⟨Node.release_protector_none_wf hc h1,
      releaseProtectorChildren_gt_wf head tail accesses (childId + 1) (by omega) hcs h2⟩

mutual

/-- Step 2 of `TreeBorrowsMemory.release_protector`: `Node.release_protector`
clears `protected := .No` at `path` and transitions all other nodes, restoring
`Node.wf sz` from `Node.wfUnprotAt sz path`. -/
theorem Node.release_protector_some_wf {sz : Nat} :
    ∀ (path : Gen.Path) {n n' : Gen.Node} {accesses : List (Option Gen.AccessKind)},
      Node.wfUnprotAt sz path n →
      Node.release_protector n (some path) accesses = .ok n' →
      Node.wf sz n'
  | [], ⟨children, permissions, prot⟩, n', _, hwf, h => by
    unfold Node.release_protector at h
    dsimp only at h
    obtain rfl := interp_pure_ok h
    exact hwf
  | head :: tail, ⟨children, permissions, prot⟩, n', accesses, ⟨hlen, hmp, hch⟩, h => by
    unfold Node.release_protector at h
    simp only [Option.isSome_some, ↓reduceIte] at h
    obtain ⟨perms', hp, h⟩ := bind_ok h
    obtain ⟨children', hcs, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    obtain ⟨hlen', hmp'⟩ :=
      Node.releaseProtectorPermissions_wf .Local prot accesses 0 permissions perms' hmp hp
    exact ⟨hlen'.trans hlen, hmp',
      Node.releaseProtectorChildren_some_wf head tail 0 hch hcs⟩

/-- Child-list companion to `Node.release_protector_some_wf`. -/
theorem Node.releaseProtectorChildren_some_wf {sz : Nat} (head : Int) (tail : Gen.Path) :
    ∀ (cur : Nat) {cs cs' : List Gen.Node} {accesses : List (Option Gen.AccessKind)},
      Node.childrenWfUnprotAt sz head tail cur cs →
      Node.releaseProtectorChildren (Int.ofNat cur) (some (head :: tail)) accesses cs = .ok cs' →
      Node.childrenWf sz cs'
  | _, [], _, _, hch, _ => False.elim hch
  | cur, c :: cs, cs', accesses, hch, h => by
    unfold Node.releaseProtectorChildren at h
    rcases hch with ⟨rfl, hc, hcs⟩ | ⟨hne, hc, hcs⟩
    · simp only [beq_self_eq_true, ↓reduceIte] at h
      obtain ⟨c', h1, h⟩ := bind_ok h
      obtain ⟨rest', h2, h⟩ := bind_ok h
      obtain rfl := interp_pure_ok h
      exact ⟨Node.release_protector_some_wf tail hc h1,
        releaseProtectorChildren_gt_wf (Int.ofNat cur) tail accesses (Int.ofNat cur + 1)
          (by omega) hcs h2⟩
    · have hbeq : (head == Int.ofNat cur) = false := beq_false_of_ne hne
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨c', h1, h⟩ := bind_ok h
      obtain ⟨rest', h2, h⟩ := bind_ok h
      obtain rfl := interp_pure_ok h
      have hcur : Int.ofNat cur + 1 = Int.ofNat (cur + 1) := rfl
      rw [hcur] at h2
      exact ⟨Node.release_protector_none_wf hc h1,
        Node.releaseProtectorChildren_some_wf head tail (cur + 1) hcs h2⟩

end

private theorem childrenWfUnprotAt_of_set {sz : Nat} {subPath : Gen.Path} {elem' : Gen.Node}
    (helem' : Node.wfUnprotAt sz subPath elem') :
    ∀ (cs : List Gen.Node) (cur k : Nat),
      k < cs.length → Node.childrenWf sz cs →
      Node.childrenWfUnprotAt sz (Int.ofNat (cur + k)) subPath cur (cs.set k elem')
  | [], _, _, hk, _ => by simp at hk
  | _ :: cs, cur, 0, _, ⟨_, hcs⟩ =>
    .inl ⟨by simp, helem', hcs⟩
  | c :: cs, cur, k + 1, hk, ⟨hc, hcs⟩ => by
    have hlt : k < cs.length := by simp at hk; omega
    have hadd : cur + (k + 1) = cur + 1 + k := by omega
    rw [hadd]
    have hne : Int.ofNat (cur + 1 + k) ≠ Int.ofNat cur := by
      intro heq
      injection heq with heq
      omega
    exact .inr ⟨hne, hc, childrenWfUnprotAt_of_set helem' cs (cur + 1) k hlt hcs⟩

private theorem access_node_wfUnprotAt {O : Type} {sz : Nat} {f : Gen.Node → Interp (O × Gen.Node)}
    (hf : ∀ u u' o, Node.wf sz u → f u = .ok (o, u') → Node.wfUnprotAt sz [] u') :
    ∀ (path : Gen.Path) {n n' : Gen.Node} {out : O},
      Node.wf sz n → Node.access_node f path n = .ok (out, n') → Node.wfUnprotAt sz path n'
  | [], n, n', out, hwf, h => hf n n' out hwf h
  | subRootId :: subPath, ⟨children, permissions, prot⟩, n', out, ⟨hlen, hmp, hch⟩, h => by
    unfold Node.access_node at h
    split at h
    · cases h
    · obtain ⟨⟨o, children'⟩, hm, h⟩ := bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
      obtain ⟨elem, elem', hge, hlt, hget, hsub, rfl⟩ := listMutateAt_ok hm
      have hch_mem : ∀ {cs : List Gen.Node}, Node.childrenWf sz cs → ∀ c ∈ cs, Node.wf sz c := by
        intro cs hcs c hc
        induction cs with
        | nil => exact False.elim (List.not_mem_nil hc)
        | cons d ds ih =>
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hcs.1
          · exact ih hcs.2 hc
      have helem' := access_node_wfUnprotAt hf subPath
        (hch_mem hch elem (List.mem_of_getElem? hget)) hsub
      have hcwf := childrenWfUnprotAt_of_set helem' children 0 subRootId.toNat hlt hch
      have hid : Int.ofNat (0 + subRootId.toNat) = subRootId := by
        rw [Nat.zero_add]
        exact Int.toNat_of_nonneg hge
      rw [hid] at hcwf
      exact ⟨hlen, hmp, hcwf⟩

/-- `TreeBorrowsMemory.release_protector` preserves `TreeBorrowsMemory.wfLive`:
every live allocation's borrow tree remains well-formed after unprotecting the
node at `provenance.2` and releasing its protector across the tree. -/
theorem TreeBorrowsMemory.release_protector_wfLive
    {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {provenance : Gen.TreeBorrowsProvenance}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.release_protector tbm provenance = .ok tbm') :
    TreeBorrowsMemory.wfLive tbm' := by
  rcases provenance with ⟨allocId, path⟩
  unfold TreeBorrowsMemory.release_protector at h
  obtain ⟨⟨_, allocations'⟩, hpair, h⟩ := bind_ok h
  dsimp only at h
  obtain rfl := interp_pure_ok h
  obtain ⟨allocation, alloc', _, _, hget, hf, rfl⟩ := listMutateAt_ok hpair
  intro alloc hm' hlive
  rcases mem_set_or hm' with rfl | hm''
  · obtain ⟨⟨protectorAccesses, root1⟩, hacc, hf⟩ := bind_ok hf
    cases halloc_live : allocation.live with
    | false =>
      simp only [halloc_live, Bool.not_false, ↓reduceIte] at hf
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hf)
      simp at hlive
    | true =>
      simp only [halloc_live, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hf
      obtain ⟨root2, hrel, hf⟩ := bind_ok hf
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hf)
      have hroot0 := hwf allocation (List.mem_of_getElem? hget) halloc_live
      have hroot1 : Node.wfUnprotAt (Allocation.size allocation).bytes path root1 := by
        refine access_node_wfUnprotAt (fun u u' o hu hfu => ?_) path hroot0 hacc
        rcases u with ⟨uch, uperms, uprot⟩
        cases hy : Protected.yes uprot with
        | false =>
          simp only [hy, Bool.not_false, ↓reduceIte] at hfu
          cases hfu
        | true =>
          simp only [hy, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfu
          obtain ⟨pairs, hmap, hfu⟩ := bind_ok hfu
          obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hfu)
          have hunp : ∀ x y, Permission.unprotect x = .ok y →
              Permission.matches_protector y.1 .No = true := by
            intro x y hx
            cases x with
            | Unprot _ => cases hx
            | Prot q =>
              obtain rfl := interp_pure_ok hx
              rfl
          obtain ⟨hpairs_len, hpairs_mp⟩ := list_mapM_loop_ok hunp uperms [] pairs hmap
            (fun _ hy' => False.elim (List.not_mem_nil hy'))
          refine ⟨by simp [hpairs_len, hu.1], fun p hp => ?_, hu.2.2⟩
          obtain ⟨pair, hpm, rfl⟩ := List.mem_map.mp hp
          exact hpairs_mp pair hpm
      exact Node.release_protector_some_wf path hroot1 hrel
  · exact hwf alloc hm'' hlive

/-- `TreeBorrowsMemory.end_call` preserves `TreeBorrowsMemory.wfLive` across the
frame's entire `protectors` release list. -/
theorem TreeBorrowsMemory.end_call_wfLive {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {extra : Gen.TreeBorrowsFrameExtra}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.end_call tbm extra = .ok tbm') :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.end_call at h
  have key : ∀ (ps : List Gen.TreeBorrowsProvenance)
      {acc out : Gen.TreeBorrowsMemory Gen.x86_64},
      TreeBorrowsMemory.wfLive acc →
      ps.foldlM (fun a prov => TreeBorrowsMemory.release_protector a prov) acc = .ok out →
      TreeBorrowsMemory.wfLive out := by
    intro ps
    induction ps with
    | nil =>
      intro acc out hacc hf
      rw [List.foldlM_nil] at hf
      obtain rfl := interp_pure_ok hf
      exact hacc
    | cons prov rest ih =>
      intro acc out hacc hf
      rw [List.foldlM_cons] at hf
      obtain ⟨mid, hr, hf⟩ := bind_ok hf
      exact ih (TreeBorrowsMemory.release_protector_wfLive hacc hr) hf
  exact key extra.protectors hwf h

/-- Every provenance carried by `ptr` refers to an existing allocation slot in `tbm`
(`spec/mem/basic.md`: "since AllocId cannot be faked"). -/
def TreeBorrowsMemory.validPtrAlloc (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) : Prop :=
  ∀ id p, ptr.provenance = some (id, p) →
    0 ≤ id._0 ∧ id._0.toNat < tbm.mem.allocations.length

private theorem check_ptr_tb_no_specPanic {tbm : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} (len : Size) (msg : String)
    (hvalid : TreeBorrowsMemory.validPtrAlloc tbm ptr) :
    BasicMemory.check_ptr tbm.mem ptr len ≠ .error (.specPanic msg) := by
  intro h
  unfold BasicMemory.check_ptr at h
  split at h
  · cases h
  · cases hprov : ptr.provenance with
    | none => simp only [hprov] at h; cases h
    | some pair =>
      rcases pair with ⟨id, provExtra⟩
      simp only [hprov] at h
      obtain ⟨hge, hlt⟩ := hvalid id provExtra hprov
      obtain ⟨alloc, hget⟩ : ∃ a, tbm.mem.allocations[id._0.toNat]? = some a :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have hidx : listIndex tbm.mem.allocations id._0 "self.allocations[id.0]" = .ok alloc := by
        simp [listIndex, hge, hget, pure, Except.pure]
      rw [hidx] at h
      dsimp only [bind, Except.bind] at h
      split at h
      · cases h
      · split at h <;> cases h

private theorem check_ptr_tb_some_ok {tbm : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {len : Size}
    {id : Gen.AllocId} {provExtra : Gen.Path} {offset : Size}
    (hck : BasicMemory.check_ptr tbm.mem ptr len = .ok (some (id, provExtra, offset))) :
    ∃ allocation,
      0 ≤ id._0 ∧ id._0.toNat < tbm.mem.allocations.length ∧
      tbm.mem.allocations[id._0.toNat]? = some allocation ∧
      listIndex tbm.mem.allocations id._0 "self.allocations[id.0]" = .ok allocation ∧
      allocation.live = true ∧
      offset.bytes + len.bytes ≤ allocation.data.length := by
  unfold BasicMemory.check_ptr at hck
  split at hck
  · cases hck
  · cases hprov : ptr.provenance with
    | none => simp only [hprov] at hck; cases hck
    | some pair =>
      rcases pair with ⟨id0, pe0⟩
      simp only [hprov] at hck
      obtain ⟨allocation, hidx, hck⟩ := bind_ok hck
      obtain ⟨hge, hlt, hget⟩ := listIndex_ok hidx
      cases hlive : allocation.live with
      | false =>
        simp only [hlive, Bool.not_false, ↓reduceIte] at hck
        cases hck
      | true =>
        simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hck
        dsimp only [Allocation.size] at hck
        by_cases hbounds :
            ptr.addr - allocation.addr < 0 ∨
              ptr.addr - allocation.addr + (len.bytes : Int) > (allocation.data.length : Int)
        · simp only [hbounds, ↓reduceIte] at hck; cases hck
        · simp only [hbounds, ↓reduceIte] at hck
          have hnn : (0 : Int) ≤ ptr.addr - allocation.addr :=
            Int.not_lt.mp fun hlt => hbounds (.inl hlt)
          have hle : ptr.addr - allocation.addr + (len.bytes : Int) ≤ (allocation.data.length : Int) :=
            Int.not_lt.mp fun hgt => hbounds (.inr hgt)
          have hinj := Option.some.inj (interp_pure_ok hck)
          obtain ⟨rfl, hpair⟩ := Prod.mk.inj hinj
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
          refine ⟨allocation, hge, hlt, hget, hidx, hlive, ?_⟩
          dsimp only
          cases hdiff : ptr.addr - allocation.addr with
          | ofNat k =>
            rw [hdiff] at hle
            exact Int.ofNat_le.mp hle
          | negSucc k =>
            rw [hdiff] at hnn
            cases hnn

/-- `TreeBorrowsMemory.allocate` never raises `Stop.specPanic`. -/
theorem TreeBorrowsMemory.allocate_no_specPanic (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (kind : Gen.AllocationKind) (size : Size) (align : Align) (msg : String) :
    TreeBorrowsMemory.allocate tbm kind size align ≠ .error (.specPanic msg) := by
  intro h
  unfold TreeBorrowsMemory.allocate BasicMemory.allocate at h
  rcases bind_err h with ha | ⟨_, _, hp⟩
  · split at ha
    · cases ha
    · split at ha <;> cases ha
  · cases hp

/-- On a `wfLive` Tree Borrows memory, `TreeBorrowsMemory.load` on any pointer
with a valid allocation ID never raises `Stop.specPanic` (every misaligned,
provenance-less, dangling, out-of-bounds, or permission-violating read cleanly
raises `Stop.ub`). -/
theorem TreeBorrowsMemory.load_no_specPanic {tbm : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} (len : Size) (align : Align)
    (msg : String)
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (hvalid : TreeBorrowsMemory.validPtrAlloc tbm ptr) :
    TreeBorrowsMemory.load tbm ptr len align ≠ .error (.specPanic msg) := by
  intro h
  unfold TreeBorrowsMemory.load BasicMemory.load at h
  rcases bind_err h with hload | ⟨_, _, hp⟩
  · split at hload
    · cases hload
    · rcases bind_err hload with hck_err | ⟨opt, hck, hload⟩
      · exact check_ptr_tb_no_specPanic len msg hvalid hck_err
      · cases opt with
        | none => cases hload
        | some triple =>
          rcases triple with ⟨id, provExtra, offset⟩
          obtain ⟨allocation, hge, hlt, hget, hidx, hlive, hbounds⟩ :=
            check_ptr_tb_some_ok hck
          dsimp only at hload
          rw [hidx] at hload
          dsimp only [bind, Except.bind] at hload
          rcases bind_err hload with hextra_err | ⟨extra', _, hload⟩
          · rcases bind_err hextra_err with hacc_err | ⟨_, _, hp⟩
            · exact Node.access_no_specPanic _ _ .Read offset len msg
                (hwf allocation (List.mem_of_getElem? hget) hlive) hbounds hacc_err
            · cases hp
          · have hset : listSet tbm.mem.allocations id._0
                { allocation with extra := extra' } "set" =
                .ok (tbm.mem.allocations.set id._0.toNat { allocation with extra := extra' }) := by
              simp [listSet, hge, hlt, pure, Except.pure]
            rw [hset] at hload
            dsimp only [bind, Except.bind] at hload
            have hsub : subsliceWithLength allocation.data (offset.bytes : Int) (len.bytes : Int) =
                .ok ((allocation.data.drop (offset.bytes : Int).toNat).take
                  (len.bytes : Int).toNat) := by
              unfold subsliceWithLength
              have hcond : (0 : Int) ≤ offset.bytes ∧ (0 : Int) ≤ len.bytes ∧
                  (offset.bytes : Int) + (len.bytes : Int) ≤ allocation.data.length :=
                ⟨by omega, by omega, by omega⟩
              simp only [hcond, and_self, ↓reduceIte]
              rfl
            rw [hsub] at hload
            cases hload
  · cases hp

/-- On a `wfLive` Tree Borrows memory, `TreeBorrowsMemory.store` on any pointer
with a valid allocation ID never raises `Stop.specPanic`. -/
theorem TreeBorrowsMemory.store_no_specPanic {tbm : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    (bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (align : Align)
    (msg : String)
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (hvalid : TreeBorrowsMemory.validPtrAlloc tbm ptr) :
    TreeBorrowsMemory.store tbm ptr bytes align ≠ .error (.specPanic msg) := by
  intro h
  unfold TreeBorrowsMemory.store BasicMemory.store at h
  rcases bind_err h with hstore | ⟨_, _, hp⟩
  · split at hstore
    · cases hstore
    · rcases bind_err hstore with hck_err | ⟨opt, hck, hstore⟩
      · exact check_ptr_tb_no_specPanic ⟨bytes.length⟩ msg hvalid hck_err
      · cases opt with
        | none => cases hstore
        | some triple =>
          rcases triple with ⟨id, provExtra, offset⟩
          obtain ⟨allocation, hge, hlt, hget, hidx, hlive, hbounds⟩ :=
            check_ptr_tb_some_ok hck
          dsimp only at hbounds
          dsimp only at hstore
          rw [hidx] at hstore
          dsimp only [bind, Except.bind] at hstore
          rcases bind_err hstore with hextra_err | ⟨extra', _, hstore⟩
          · rcases bind_err hextra_err with hacc_err | ⟨_, _, hp⟩
            · exact Node.access_no_specPanic _ _ .Write offset ⟨bytes.length⟩ msg
                (hwf allocation (List.mem_of_getElem? hget) hlive) hbounds hacc_err
            · cases hp
          · have hws : writeSubsliceAtIndex allocation.data (offset.bytes : Int) bytes =
                .ok (allocation.data.take (offset.bytes : Int).toNat ++ bytes ++
                  allocation.data.drop ((offset.bytes : Int).toNat + bytes.length)) := by
              unfold writeSubsliceAtIndex
              have hcond : (0 : Int) ≤ offset.bytes ∧
                  (offset.bytes : Int) + (bytes.length : Int) ≤ allocation.data.length :=
                ⟨by omega, by omega⟩
              simp only [hcond, and_self, ↓reduceIte]
              rfl
            rw [hws] at hstore
            dsimp only [bind, Except.bind] at hstore
            have hset : listSet tbm.mem.allocations id._0
                { allocation with
                  data := allocation.data.take (offset.bytes : Int).toNat ++ bytes ++
                    allocation.data.drop ((offset.bytes : Int).toNat + bytes.length),
                  extra := extra' } "set" =
                .ok (tbm.mem.allocations.set id._0.toNat
                  { allocation with
                    data := allocation.data.take (offset.bytes : Int).toNat ++ bytes ++
                      allocation.data.drop ((offset.bytes : Int).toNat + bytes.length),
                    extra := extra' }) := by
              simp [listSet, hge, hlt, pure, Except.pure]
            rw [hset] at hstore
            cases hstore
  · cases hp

/-- On a `wfLive` Tree Borrows memory, `TreeBorrowsMemory.deallocate` on any
pointer with a valid allocation ID never raises `Stop.specPanic`. -/
theorem TreeBorrowsMemory.deallocate_no_specPanic {tbm : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} (kind : Gen.AllocationKind)
    (size : Size) (align : Align) (msg : String)
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (hvalid : TreeBorrowsMemory.validPtrAlloc tbm ptr) :
    TreeBorrowsMemory.deallocate tbm ptr kind size align ≠ .error (.specPanic msg) := by
  intro h
  unfold TreeBorrowsMemory.deallocate BasicMemory.deallocate at h
  rcases bind_err h with hd | ⟨_, _, hp⟩
  · cases hprov : ptr.provenance with
    | none => simp only [hprov] at hd; cases hd
    | some pair =>
      rcases pair with ⟨id, provExtra⟩
      simp only [hprov] at hd
      obtain ⟨hge, hlt⟩ := hvalid id provExtra hprov
      obtain ⟨allocation, hget⟩ : ∃ a, tbm.mem.allocations[id._0.toNat]? = some a :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have hidx : listIndex tbm.mem.allocations id._0 "self.allocations[id.0]" =
          .ok allocation := by
        simp [listIndex, hge, hget, pure, Except.pure]
      rw [hidx] at hd
      dsimp only [bind, Except.bind] at hd
      cases hlive : allocation.live with
      | false =>
        simp only [hlive, Bool.not_false, ↓reduceIte] at hd
        cases hd
      | true =>
        simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hd
        split at hd; · cases hd
        split at hd; · dsimp only [ub] at hd; cases hd
        by_cases hsz : size = Allocation.size allocation
        · simp only [hsz, ne_eq, not_true_eq_false, ↓reduceIte] at hd
          split at hd; · cases hd
          rcases bind_err hd with hextra_err | ⟨extra', _, hd⟩
          · rcases bind_err hextra_err with hacc_err | ⟨root', _, hextra_err⟩
            · exact Node.access_no_specPanic _ _ .Write ⟨0⟩ (Allocation.size allocation) msg
                (hwf allocation (List.mem_of_getElem? hget) hlive)
                (by change 0 + allocation.data.length ≤ allocation.data.length; omega) hacc_err
            · split at hextra_err <;> cases hextra_err
          · have hset : listSet tbm.mem.allocations id._0
                { allocation with live := false, extra := extra' } "set" =
                .ok (tbm.mem.allocations.set id._0.toNat
                  { allocation with live := false, extra := extra' }) := by
              simp [listSet, hge, hlt, pure, Except.pure]
            rw [hset] at hd
            cases hd
        · simp only [ne_eq, hsz, not_false_eq_true, ↓reduceIte] at hd; cases hd
  · cases hp

/-- `TreeBorrowsMemory.new` satisfies `TreeBorrowsMemory.wfLive`. -/
theorem TreeBorrowsMemory.new_wfLive (params : Gen.TreeBorrowsParams) :
    TreeBorrowsMemory.wfLive (TreeBorrowsMemory.new params) :=
  TreeBorrowsMemory.wfLive_of_wf (TreeBorrowsMemory.new_wf params)

/-- `TreeBorrowsMemory.allocate` preserves `TreeBorrowsMemory.wfLive`. -/
theorem TreeBorrowsMemory.allocate_wfLive {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {kind : Gen.AllocationKind} {size : Size} {align : Align}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.allocate tbm kind size align = .ok (ptr, tbm')) :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.allocate BasicMemory.allocate at h
  obtain ⟨⟨ptr1, mem'⟩, halloc, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  split at halloc
  · cases halloc
  · cases hpick : BasicMemory.pickAddr tbm.mem size align with
    | none => simp only [hpick] at halloc; cases halloc
    | some addr =>
      simp only [hpick] at halloc
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok halloc)
      intro alloc hm hlive
      rcases List.mem_append.mp hm with hm | hm
      · exact hwf alloc hm hlive
      · rw [List.mem_singleton.mp hm]
        refine ⟨by simp [Allocation.size], fun p hp => ?_, trivial⟩
        rw [List.eq_of_mem_replicate hp]
        rfl

/-- `TreeBorrowsMemory.load` preserves `TreeBorrowsMemory.wfLive`. -/
theorem TreeBorrowsMemory.load_wfLive {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {len : Size} {align : Align}
    {bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.load tbm ptr len align = .ok (bytes, tbm')) :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.load BasicMemory.load at h
  obtain ⟨⟨bs, mem'⟩, hload, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  split at hload
  · cases hload
  · obtain ⟨opt, _, hload⟩ := bind_ok hload
    cases opt with
    | none =>
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hload)
      exact hwf
    | some triple =>
      rcases triple with ⟨id, provExtra, offset⟩
      obtain ⟨allocation, hidx, hload⟩ := bind_ok hload
      obtain ⟨extra', hextra, hload⟩ := bind_ok hload
      obtain ⟨allocations', hset, hload⟩ := bind_ok hload
      obtain ⟨_, _, hload⟩ := bind_ok hload
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hload)
      obtain ⟨root', hacc, hextra⟩ := bind_ok hextra
      obtain rfl := interp_pure_ok hextra
      obtain ⟨_, _, rfl⟩ := listSet_ok hset
      obtain ⟨_, _, hget⟩ := listIndex_ok hidx
      intro alloc hm hlive
      rcases mem_set_or hm with rfl | hm'
      · exact Node.access_wf (hwf allocation (List.mem_of_getElem? hget) hlive) hacc
      · exact hwf alloc hm' hlive

/-- `TreeBorrowsMemory.store` preserves `TreeBorrowsMemory.wfLive`. -/
theorem TreeBorrowsMemory.store_wfLive {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    {bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)} {align : Align}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.store tbm ptr bytes align = .ok tbm') :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.store BasicMemory.store at h
  obtain ⟨mem', hstore, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  split at hstore
  · cases hstore
  · obtain ⟨opt, _, hstore⟩ := bind_ok hstore
    cases opt with
    | none =>
      obtain rfl := interp_pure_ok hstore
      exact hwf
    | some triple =>
      rcases triple with ⟨id, provExtra, offset⟩
      obtain ⟨allocation, hidx, hstore⟩ := bind_ok hstore
      obtain ⟨extra', hextra, hstore⟩ := bind_ok hstore
      obtain ⟨data', hws, hstore⟩ := bind_ok hstore
      obtain ⟨allocations', hset, hstore⟩ := bind_ok hstore
      obtain rfl := interp_pure_ok hstore
      obtain ⟨root', hacc, hextra⟩ := bind_ok hextra
      obtain rfl := interp_pure_ok hextra
      obtain ⟨_, _, rfl⟩ := listSet_ok hset
      obtain ⟨_, _, hget⟩ := listIndex_ok hidx
      have hdata_len := (writeSubsliceAtIndex_ok hws).2.2.1
      intro alloc hm hlive
      rcases mem_set_or hm with rfl | hm'
      · dsimp only [Allocation.size]
        rw [hdata_len]
        exact Node.access_wf (hwf allocation (List.mem_of_getElem? hget) hlive) hacc
      · exact hwf alloc hm' hlive

/-- `TreeBorrowsMemory.deallocate` preserves `TreeBorrowsMemory.wfLive` (the
deallocated slot is marked `live := false`). -/
theorem TreeBorrowsMemory.deallocate_wfLive {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {kind : Gen.AllocationKind}
    {size : Size} {align : Align}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.deallocate tbm ptr kind size align = .ok tbm') :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.deallocate BasicMemory.deallocate at h
  obtain ⟨mem', hdealloc, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  cases hprov : ptr.provenance with
  | none => simp only [hprov] at hdealloc; cases hdealloc
  | some pair =>
    rcases pair with ⟨id, provExtra⟩
    simp only [hprov] at hdealloc
    obtain ⟨allocation, _, hdealloc⟩ := bind_ok hdealloc
    split at hdealloc; · cases hdealloc
    split at hdealloc; · cases hdealloc
    split at hdealloc; · dsimp only [ub] at hdealloc; cases hdealloc
    split at hdealloc; · cases hdealloc
    split at hdealloc; · cases hdealloc
    obtain ⟨extra', _, hdealloc⟩ := bind_ok hdealloc
    obtain ⟨allocations', hset, hdealloc⟩ := bind_ok hdealloc
    obtain rfl := interp_pure_ok hdealloc
    obtain ⟨_, _, rfl⟩ := listSet_ok hset
    intro alloc hm hlive
    rcases mem_set_or hm with rfl | hm'
    · simp at hlive
    · exact hwf alloc hm' hlive

/-- `TreeBorrowsMemory.reborrow` preserves `TreeBorrowsMemory.wfLive` (including
for zero-sized reborrows, since `reborrow` preserves `allocation.live` and
`allocation.data`). -/
theorem TreeBorrowsMemory.reborrow_wfLive {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr ptr' : Gen.ThinPointer Gen.TreeBorrowsProvenance} {settings : Gen.ReborrowSettings}
    {fe fe' : Gen.TreeBorrowsFrameExtra}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.reborrow tbm ptr settings fe = .ok (ptr', tbm', fe')) :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.reborrow at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases hprov : ptr.provenance with
  | none =>
    simp only [hprov] at h
    split at h
    · cases h
    · obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
      obtain ⟨rfl, _⟩ := Prod.mk.inj h
      exact hwf
  | some pair =>
    rcases pair with ⟨allocId, parentPath⟩
    simp only [hprov] at h
    obtain ⟨⟨childPath, allocations'⟩, hm, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    obtain ⟨allocation, alloc', _, _, hget, hf, rfl⟩ := listMutateAt_ok hm
    cases hoff : Size.from_bytes (ptr.addr - allocation.addr) with
    | none => simp [hoff, specPanic, bind, Except.bind] at hf
    | some offset =>
      simp only [hoff, pure, Except.pure, bind, Except.bind] at hf
      have hbody : ∀ (permissions : List Gen.Permission),
          permissions.length = (Allocation.size allocation).bytes →
          (let childNode : Gen.Node :=
            { children := [], permissions := permissions, «protected» := settings.«protected» }
           if (!childNode.permissions.all fun x =>
               Permission.matches_protector x childNode.«protected») = true then
             specPanic
               "assertion failed: child_node.permissions.all(|x| x.matches_protector(child_node.protected))"
           else do
             let (cp, root1) ← Node.add_node allocation.extra.root parentPath childNode
             let root2 ← TreeBorrowsMemory.reborrowInitAccess cp offset 0 settings.inside root1
             pure (cp, { data := allocation.data, addr := allocation.addr, align := allocation.align,
                         kind := allocation.kind, live := allocation.live, extra := { root := root2 } })) =
            .ok (childPath, alloc') →
          TreeBorrowsMemory.wfLive
            { params := tbm.params,
              mem := { allocations := tbm.mem.allocations.set allocId._0.toNat alloc',
                       _phantom := tbm.mem._phantom } } := by
        intro permissions hplen hfb
        dsimp only at hfb
        cases hall : permissions.all (fun x => Permission.matches_protector x settings.«protected») with
        | false =>
          simp only [hall, Bool.not_false, ↓reduceIte] at hfb
          cases hfb
        | true =>
          simp only [hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfb
          obtain ⟨⟨cp, root1⟩, hadd, hfb⟩ := bind_ok hfb
          dsimp only at hfb
          obtain ⟨root2, hinit, hfb⟩ := bind_ok hfb
          obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hfb)
          have hchild_wf : Node.wf (Allocation.size allocation).bytes
              { children := [], permissions := permissions, «protected» := settings.«protected» } :=
            ⟨hplen, List.all_eq_true.mp hall, trivial⟩
          intro alloc hm' hlive
          rcases mem_set_or hm' with rfl | hm''
          · have hr1 := Node.add_node_wf
              (hwf allocation (List.mem_of_getElem? hget) hlive) hchild_wf hadd
            exact TreeBorrowsMemory.reborrowInitAccess_wf cp offset 0 settings.inside hr1 hinit
          · exact hwf alloc hm'' hlive
      by_cases hgt : settings.inside.length > 0
      · simp only [hgt, ↓reduceIte] at hf
        obtain ⟨permissions, hps, hf⟩ := bind_ok hf
        exact hbody permissions
          ((writeSubsliceAtIndex_ok hps).2.2.1.trans (List.length_replicate ..)) hf
      · simp only [hgt, ↓reduceIte] at hf
        exact hbody _ (List.length_replicate ..) hf

/-- `TreeBorrowsMemory.retag_ptr` preserves `TreeBorrowsMemory.wfLive`. -/
theorem TreeBorrowsMemory.retag_ptr_wfLive {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {fe fe' : Gen.TreeBorrowsFrameExtra} {ptr ptr' : Gen.Pointer Gen.TreeBorrowsProvenance}
    {ptrType : Gen.PtrType} {fnEntry fnImplicitWrites : Bool}
    {vtableLookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.retag_ptr tbm fe ptr ptrType fnEntry fnImplicitWrites vtableLookup =
      .ok (ptr', tbm', fe')) :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.retag_ptr at h
  obtain ⟨opt, _, h⟩ := bind_ok h
  cases opt with
  | none =>
    obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    exact hwf
  | some perms =>
    obtain ⟨⟨thin', tbm1, fe1⟩, hreb, h⟩ := bind_ok h
    obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    exact TreeBorrowsMemory.reborrow_wfLive hwf hreb

/-- Machine-level Tree Borrows live-allocation invariant on `MachTB`
(`Machine<TreeBorrowsMemory<x86_64>>`): every live allocation in `m` carries a
well-formed borrow tree (`Node.wf`). -/
def MachTB.wfLive (m : MachTB) : Prop :=
  TreeBorrowsMemory.wfLive m.mem.memory

private theorem cm_tb_load_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {len : Size} {align : Align}
    {atomicity : Gen.Atomicity}
    {bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.load cm ptr len align atomicity = .ok (bytes, cm')) :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.load at h
  obtain ⟨⟨_, mem'⟩, hload, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  exact TreeBorrowsMemory.load_wfLive hwf hload

private theorem cm_tb_store_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    {bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)} {align : Align}
    {atomicity : Gen.Atomicity}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.store cm ptr bytes align atomicity = .ok cm') :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.store at h
  obtain ⟨mem', hstore, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  exact TreeBorrowsMemory.store_wfLive hwf hstore

private theorem cm_tb_deinit_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {len : Size} {align : Align}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.deinit cm ptr len align = .ok cm') :
    TreeBorrowsMemory.wfLive cm'.memory :=
  cm_tb_store_wfLive hwf h

private theorem cm_tb_allocate_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {kind : Gen.AllocationKind} {size : Size} {align : Align}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.allocate cm kind size align = .ok (ptr, cm')) :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.allocate at h
  obtain ⟨⟨_, mem'⟩, halloc, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  exact TreeBorrowsMemory.allocate_wfLive hwf halloc

private theorem cm_tb_deallocate_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {kind : Gen.AllocationKind}
    {size : Size} {align : Align}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.deallocate cm ptr kind size align = .ok cm') :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.deallocate at h
  obtain ⟨mem', hdealloc, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  exact TreeBorrowsMemory.deallocate_wfLive hwf hdealloc

private theorem cm_tb_retag_ptr_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {fe fe' : Gen.TreeBorrowsFrameExtra} {ptr ptr' : Gen.Pointer Gen.TreeBorrowsProvenance}
    {ptrType : Gen.PtrType} {fnEntry fnImplicitWrites : Bool}
    {vtableLookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.retag_ptr cm fe ptr ptrType fnEntry fnImplicitWrites vtableLookup =
      .ok (ptr', cm', fe')) :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.retag_ptr at h
  obtain ⟨⟨_, mem', _⟩, hret, h⟩ := bind_ok h
  obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
  obtain ⟨rfl, _⟩ := Prod.mk.inj h
  exact TreeBorrowsMemory.retag_ptr_wfLive hwf hret

private theorem cm_tb_end_call_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {extra : Gen.TreeBorrowsFrameExtra}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.end_call cm extra = .ok cm') :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.end_call at h
  obtain ⟨mem', hend, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  exact TreeBorrowsMemory.end_call_wfLive hwf hend

private theorem mutateCurFrameM_tb_wfLive {m m' : MachTB}
    {f : Gen.StackFrame TBM → Gen.StackFrame TBM}
    (hwf : MachTB.wfLive m) (h : mutateCurFrameM m f = .ok m') :
    MachTB.wfLive m' := by
  unfold mutateCurFrameM at h
  obtain ⟨t, _, h⟩ := bind_ok h
  cases hlast : t.stack.getLast? with
  | none => simp only [hlast] at h; cases h
  | some fr =>
    simp only [hlast] at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    exact hwf

private theorem jumpToBlockM_tb_wfLive {m m' : MachTB} {b : Gen.BbName}
    (hwf : MachTB.wfLive m) (h : jumpToBlockM m b = .ok m') :
    MachTB.wfLive m' :=
  mutateCurFrameM_tb_wfLive hwf h

private theorem terminateActiveThreadM_tb_wfLive {m m' : MachTB}
    (hwf : MachTB.wfLive m) (h : terminateActiveThreadM m = .ok m') :
    MachTB.wfLive m' := by
  unfold terminateActiveThreadM at h
  dsimp only at h
  by_cases ha : m.active_thread = 0
  · simp only [ha, ↓reduceIte] at h; cases h
  · simp only [ha, ↓reduceIte] at h
    obtain ⟨t, _, h⟩ := bind_ok h
    by_cases hst : t.stack.length = 0
    · simp only [hst, ne_eq, not_true_eq_false, ↓reduceIte] at h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain rfl := interp_pure_ok h
      exact hwf
    · simp only [ne_eq, hst, not_false_eq_true, ↓reduceIte] at h; cases h

private theorem mutateCurFrameOutM_tb_wfLive {α : Type} {m m' : MachTB} {out : α}
    {f : Gen.StackFrame TBM → Gen.ConcurrentMemory TBM →
      Interp (α × Gen.StackFrame TBM × Gen.ConcurrentMemory TBM)}
    (hf : ∀ fr o fr' cm', f fr m.mem = .ok (o, fr', cm') → TreeBorrowsMemory.wfLive cm'.memory)
    (h : mutateCurFrameOutM m f = .ok (out, m')) :
    MachTB.wfLive m' := by
  unfold mutateCurFrameOutM at h
  obtain ⟨t, _, h⟩ := bind_ok h
  cases hlast : t.stack.getLast? with
  | none => simp only [hlast] at h; cases h
  | some fr =>
    simp only [hlast] at h
    obtain ⟨⟨o, fr', cm'⟩, hfr, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hf fr o fr' cm' hfr

private theorem tryMutateCurFrameM_tb_wfLive {m m' : MachTB}
    {f : Gen.StackFrame TBM → Gen.ConcurrentMemory TBM →
      Interp (Gen.StackFrame TBM × Gen.ConcurrentMemory TBM)}
    (hf : ∀ fr fr' cm', f fr m.mem = .ok (fr', cm') → TreeBorrowsMemory.wfLive cm'.memory)
    (h : tryMutateCurFrameM m f = .ok m') :
    MachTB.wfLive m' := by
  unfold tryMutateCurFrameM at h
  obtain ⟨t, _, h⟩ := bind_ok h
  cases hlast : t.stack.getLast? with
  | none => simp only [hlast] at h; cases h
  | some fr =>
    simp only [hlast] at h
    obtain ⟨⟨fr', cm'⟩, hfr, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    exact hf fr fr' cm' hfr

/-- `typedLoadM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem typedLoadM_tb_wfLive {m m' : MachTB}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {ty : Gen.Type}
    {align : Align} {atomicity : Gen.Atomicity} {val : Gen.Value TBM}
    (hwf : MachTB.wfLive m)
    (h : typedLoadM m ptr ty align atomicity = .ok (val, m')) :
    MachTB.wfLive m' := by
  unfold typedLoadM at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨bytes, cm⟩, hload, h⟩ := bind_ok h
  dsimp only at h
  have hcm := cm_tb_load_wfLive hwf hload
  obtain ⟨opt, _, h⟩ := bind_ok h
  cases opt with
  | none => cases h
  | some v =>
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hcm

/-- `typedStoreM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem typedStoreM_tb_wfLive {m m' : MachTB}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {val : Gen.Value TBM}
    {ty : Gen.Type} {align : Align} {atomicity : Gen.Atomicity}
    (hwf : MachTB.wfLive m)
    (h : typedStoreM m ptr val ty align atomicity = .ok m') :
    MachTB.wfLive m' := by
  unfold typedStoreM at h
  dsimp only at h
  rcases hcv : checkValueM val ty (some m) with _ | ⟨⟩
  · simp only [hcv] at h; cases h
  · simp only [hcv] at h
    obtain ⟨bytes, _, h⟩ := bind_ok h
    obtain ⟨cm, hstore, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    exact cm_tb_store_wfLive hwf hstore

/-- `placeLoadM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem placeLoadM_tb_wfLive {m m' : MachTB} {place : Gen.Place TBM}
    {ty : Gen.Type} {val : Gen.Value TBM}
    (hwf : MachTB.wfLive m) (h : placeLoadM m place ty = .ok (val, m')) :
    MachTB.wfLive m' := by
  unfold placeLoadM at h
  cases hpa : place.aligned with
  | false => simp only [hpa, Bool.not_false, ↓reduceIte] at h; cases h
  | true => simp only [hpa, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; exact typedLoadM_tb_wfLive hwf h

/-- `placeStoreM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem placeStoreM_tb_wfLive {m m' : MachTB} {place : Gen.Place TBM}
    {val : Gen.Value TBM} {ty : Gen.Type}
    (hwf : MachTB.wfLive m) (h : placeStoreM m place val ty = .ok m') :
    MachTB.wfLive m' := by
  unfold placeStoreM at h
  cases hpa : place.aligned with
  | false => simp only [hpa, Bool.not_false, ↓reduceIte] at h; cases h
  | true => simp only [hpa, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; exact typedStoreM_tb_wfLive hwf h

mutual

/-- `evalPlaceM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem evalPlaceM_tb_wfLive :
    ∀ (pe : Gen.PlaceExpr) {m m' : MachTB} {out : Gen.Place TBM × Gen.Type},
      MachTB.wfLive m → evalPlaceM m pe = .ok (out, m') → MachTB.wfLive m'
  | .Local name, m, _, _, hwf, h => by
    unfold evalPlaceM at h
    obtain ⟨fr, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    cases hmg : mapGet fr.locals name with
    | none => simp only [hmg] at h; cases h
    | some _ =>
      simp only [hmg] at h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
      exact hwf
  | .Field root field, _, _, _, hwf, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨⟨rootPl, ty⟩, m1⟩, hr, h⟩ := bind_ok h
    dsimp only at h
    have hm1 := evalPlaceM_tb_wfLive root hwf hr
    cases ty with
    | Tuple sizedFields sizedHeadLayout unsizedField =>
      dsimp only at h
      by_cases h1 : 0 ≤ field ∧ field < (sizedFields.length : Int)
      · simp only [h1] at h
        obtain ⟨⟨offset, fieldTy⟩, _, h⟩ := bind_ok h
        dsimp only at h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨rootSize, _, h⟩ := bind_ok h
        by_cases hle : offset.bytes ≤ rootSize.bytes
        · simp only [hle, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
          exact hm1
        · simp only [hle, decide_false, Bool.not_false, ↓reduceIte] at h; cases h
      · simp only [h1, ↓reduceIte] at h
        by_cases h2 : field = (sizedFields.length : Int)
        · simp only [h2, ↓reduceIte] at h
          cases unsizedField with
          | none => cases h
          | some tailTy =>
            dsimp only at h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨tailAlign, _, h⟩ := bind_ok h
            dsimp only [pure, Except.pure, bind, Except.bind] at h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨rootSize, _, h⟩ := bind_ok h
            by_cases hle : (TupleHeadLayout.tail_offset sizedHeadLayout tailAlign).bytes ≤ rootSize.bytes
            · simp only [hle, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
              obtain ⟨_, _, h⟩ := bind_ok h
              obtain ⟨_, _, h⟩ := bind_ok h
              obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
              exact hm1
            · simp only [hle, decide_false, Bool.not_false, ↓reduceIte] at h; cases h
        · simp only [h2, ↓reduceIte] at h; cases h
    | Union fields _ _ _ =>
      dsimp only at h
      obtain ⟨⟨offset, fieldTy⟩, _, h⟩ := bind_ok h
      dsimp only at h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨rootSize, _, h⟩ := bind_ok h
      by_cases hle : offset.bytes ≤ rootSize.bytes
      · simp only [hle, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
        exact hm1
      · simp only [hle, decide_false, Bool.not_false, ↓reduceIte] at h; cases h
    | _ => cases h
  | .Index root index, _, _, _, hwf, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨⟨rootPl, ty⟩, m1⟩, hr, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨⟨⟨idxVal, _⟩, m2⟩, hi, h⟩ := bind_ok h
    dsimp only at h
    have hm2 := evalValueM_tb_wfLive index (evalPlaceM_tb_wfLive root hwf hr) hi
    cases idxVal with
    | Int idx =>
      dsimp only [pure, Except.pure, bind, Except.bind] at h
      cases ty with
      | Array elemTy count =>
        dsimp only [pure, Except.pure, bind, Except.bind] at h
        by_cases hob : idx < 0 ∨ idx ≥ count
        · simp only [hob, ↓reduceIte] at h; cases h
        · simp only [hob, ↓reduceIte] at h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨offset, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨rootSize, _, h⟩ := bind_ok h
          by_cases hle : offset.bytes ≤ rootSize.bytes
          · simp only [hle, ↓reduceIte] at h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
            exact hm2
          · simp only [hle, ↓reduceIte] at h; cases h
      | Slice elemTy =>
        dsimp only at h
        rcases hmeta : rootPl.ptr.metadata with _ | (count | _) <;> simp only [hmeta] at h
        · cases h
        · by_cases hob : idx < 0 ∨ idx ≥ count
          · simp only [hob, ↓reduceIte] at h; cases h
          · simp only [hob, ↓reduceIte] at h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨offset, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨rootSize, _, h⟩ := bind_ok h
            by_cases hle : offset.bytes ≤ rootSize.bytes
            · simp only [hle, ↓reduceIte] at h
              obtain ⟨_, _, h⟩ := bind_ok h
              obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
              exact hm2
            · simp only [hle, ↓reduceIte] at h; cases h
        · cases h
      | _ => cases h
    | _ => cases h
  | .Deref operand _, _, _, _, hwf, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨⟨v, vTy⟩, m1⟩, hv, h⟩ := bind_ok h
    dsimp only at h
    have hm1 := evalValueM_tb_wfLive operand hwf hv
    cases v with
    | Ptr ptr =>
      cases vTy with
      | Ptr ptrType =>
        dsimp only at h
        cases hsp : PtrType.safe_pointee ptrType with
        | none =>
          simp only [hsp, pure, Except.pure, bind, Except.bind] at h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
          exact hm1
        | some pointee =>
          simp only [hsp] at h
          obtain ⟨pointeeAlign, _, h⟩ := bind_ok h
          cases hal : Align.is_aligned pointeeAlign ptr.thin_pointer.addr with
          | false => simp only [hal, Bool.not_false, ↓reduceIte] at h; cases h
          | true =>
            simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
            exact hm1
      | _ => cases h
    | _ => cases h
  | .Downcast _ _, _, _, _, _, h => by
    unfold evalPlaceM at h; cases h

/-- `evalValueM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem evalValueM_tb_wfLive :
    ∀ (ve : Gen.ValueExpr) {m m' : MachTB} {out : Gen.Value TBM × Gen.Type},
      MachTB.wfLive m → evalValueM m ve = .ok (out, m') → MachTB.wfLive m'
  | .Constant _ _, _, _, _, hwf, h => by
    unfold evalValueM at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | .Tuple exprs _, _, _, _, hwf, h => by
    unfold evalValueM at h
    obtain ⟨⟨_, m1⟩, hes, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact evalValuesM_tb_wfLive exprs hwf hes
  | .Load source, _, _, _, hwf, h => by
    unfold evalValueM at h
    obtain ⟨⟨⟨place, ty⟩, m1⟩, hp, h⟩ := bind_ok h
    obtain ⟨⟨_, m2⟩, hl, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact placeLoadM_tb_wfLive (evalPlaceM_tb_wfLive source hwf hp) hl
  | .AddrOf target _, _, _, _, hwf, h => by
    unfold evalValueM at h
    obtain ⟨⟨_, m1⟩, hp, h⟩ := bind_ok h
    have hm1 := evalPlaceM_tb_wfLive target hwf hp
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨_, m2⟩, hm, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    refine mutateCurFrameOutM_tb_wfLive (fun fr o fr' cm' hfr => ?_) hm
    obtain ⟨⟨_, cm1, _⟩, hret, hfr⟩ := bind_ok hfr
    obtain ⟨_, hfr⟩ := Prod.mk.inj (interp_pure_ok hfr)
    obtain ⟨_, rfl⟩ := Prod.mk.inj hfr
    exact cm_tb_retag_ptr_wfLive hm1 hret
  | .UnOp _ operand, _, _, _, hwf, h => by
    unfold evalValueM at h
    obtain ⟨⟨_, m1⟩, ho, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact evalValueM_tb_wfLive operand hwf ho
  | .BinOp operator left right, _, _, _, hwf, h => by
    cases operator <;> {
      unfold evalValueM at h
      obtain ⟨⟨_, m1⟩, hl, h⟩ := bind_ok h
      obtain ⟨⟨_, m2⟩, hr, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
      exact evalValueM_tb_wfLive right (evalValueM_tb_wfLive left hwf hl) hr
    }
  | .Union _ _ _, _, _, _, _, h => by unfold evalValueM at h; cases h
  | .Variant _ _ _, _, _, _, _, h => by unfold evalValueM at h; cases h
  | .GetDiscriminant _, _, _, _, _, h => by unfold evalValueM at h; cases h

/-- `evalValuesM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem evalValuesM_tb_wfLive :
    ∀ (es : List Gen.ValueExpr) {m m' : MachTB} {vals : List (Gen.Value TBM)},
      MachTB.wfLive m → evalValuesM m es = .ok (vals, m') → MachTB.wfLive m'
  | [], _, _, _, hwf, h => by
    unfold evalValuesM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | e :: es, _, _, _, hwf, h => by
    unfold evalValuesM at h
    obtain ⟨⟨_, m1⟩, he, h⟩ := bind_ok h
    obtain ⟨⟨_, m2⟩, hes, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact evalValuesM_tb_wfLive es (evalValueM_tb_wfLive e hwf he) hes

end

/-- `storageDeadM` on `TBM` preserves `TreeBorrowsMemory.wfLive`. -/
theorem storageDeadM_tb_wfLive {fr fr' : Gen.StackFrame TBM}
    {cm cm' : Gen.ConcurrentMemory TBM} {local_ : Gen.LocalName}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : storageDeadM fr cm local_ = .ok (fr', cm')) :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold storageDeadM at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  rcases hrem : mapRemove fr.locals local_ with ⟨_ | ptr, locals⟩
  · simp only [hrem] at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  · simp only [hrem] at h
    obtain ⟨cm1, hd, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact cm_tb_deallocate_wfLive hwf hd

/-- `storageLiveM` on `TBM` preserves `TreeBorrowsMemory.wfLive`. -/
theorem storageLiveM_tb_wfLive {fr fr' : Gen.StackFrame TBM}
    {cm cm' : Gen.ConcurrentMemory TBM} {local_ : Gen.LocalName}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : storageLiveM fr cm local_ = .ok (fr', cm')) :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold storageLiveM at h
  obtain ⟨⟨fr2, cm2⟩, hsd, h⟩ := bind_ok h
  have hcm2 := storageDeadM_tb_wfLive hwf hsd
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨_, cm3⟩, ha, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  exact cm_tb_allocate_wfLive hcm2 ha

mutual

/-- `retagValM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem retagValM_tb_wfLive :
    ∀ (val : Gen.Value TBM) (ty : Gen.Type) {m m' : MachTB} {fnEntry : Bool}
      {val' : Gen.Value TBM},
      MachTB.wfLive m → retagValM m fnEntry val ty = .ok (val', m') → MachTB.wfLive m'
  | .Int _, _, _, _, _, _, hwf, h => by
    unfold retagValM at h; obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h); exact hwf
  | .Bool _, _, _, _, _, _, hwf, h => by
    unfold retagValM at h; obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h); exact hwf
  | .Union _, _, _, _, _, _, hwf, h => by
    unfold retagValM at h; obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h); exact hwf
  | .Ptr ptr, .Ptr ptrType, _, _, _, _, hwf, h => by
    unfold retagValM at h
    obtain ⟨⟨_, m1⟩, hm, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    refine mutateCurFrameOutM_tb_wfLive (fun fr o fr' cm' hfr => ?_) hm
    obtain ⟨⟨_, cm1, _⟩, hret, hfr⟩ := bind_ok hfr
    obtain ⟨_, hfr⟩ := Prod.mk.inj (interp_pure_ok hfr)
    obtain ⟨_, rfl⟩ := Prod.mk.inj hfr
    exact cm_tb_retag_ptr_wfLive hwf hret
  | .Ptr _, .Int _, _, _, _, _, _, h | .Ptr _, .Bool, _, _, _, _, _, h
  | .Ptr _, .Union _ _ _ _, _, _, _, _, _, h | .Ptr _, .Tuple _ _ _, _, _, _, _, _, h
  | .Ptr _, .Array _ _, _, _, _, _, _, h | .Ptr _, .Enum _ _ _ _ _, _, _, _, _, _, h
  | .Ptr _, .Slice _, _, _, _, _, _, h | .Ptr _, .TraitObject _, _, _, _, _, _, h => by
    unfold retagValM at h; cases h
  | .Tuple vals, .Tuple sizedFields _ _, _, _, _, _, hwf, h => by
    unfold retagValM at h
    obtain ⟨⟨_, m1⟩, ht, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact retagTupleFieldsM_tb_wfLive vals sizedFields hwf ht
  | .Tuple vals, .Array elemTy _, _, _, _, _, hwf, h => by
    unfold retagValM at h
    obtain ⟨⟨_, m1⟩, ha, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact retagArrayElemsM_tb_wfLive elemTy vals hwf ha
  | .Tuple _, .Int _, _, _, _, _, _, h | .Tuple _, .Bool, _, _, _, _, _, h
  | .Tuple _, .Union _ _ _ _, _, _, _, _, _, h | .Tuple _, .Ptr _, _, _, _, _, _, h
  | .Tuple _, .Enum _ _ _ _ _, _, _, _, _, _, h | .Tuple _, .Slice _, _, _, _, _, _, h
  | .Tuple _, .TraitObject _, _, _, _, _, _, h => by
    unfold retagValM at h; cases h
  | .Variant discriminant data, .Enum variants _ _ _ _, _, _, _, _, hwf, h => by
    unfold retagValM at h
    obtain ⟨variant, _, h⟩ := bind_ok h
    obtain ⟨⟨_, m1⟩, hr, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact retagValM_tb_wfLive data variant.ty hwf hr
  | .Variant _ _, .Int _, _, _, _, _, _, h | .Variant _ _, .Bool, _, _, _, _, _, h
  | .Variant _ _, .Union _ _ _ _, _, _, _, _, _, h | .Variant _ _, .Ptr _, _, _, _, _, _, h
  | .Variant _ _, .Tuple _ _ _, _, _, _, _, _, h | .Variant _ _, .Array _ _, _, _, _, _, _, h
  | .Variant _ _, .Slice _, _, _, _, _, _, h | .Variant _ _, .TraitObject _, _, _, _, _, _, h => by
    unfold retagValM at h; cases h

/-- `retagTupleFieldsM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem retagTupleFieldsM_tb_wfLive :
    ∀ (vals : List (Gen.Value TBM)) (fields : List (Gen.Offset × Gen.Type))
      {m m' : MachTB} {fnEntry : Bool} {vals' : List (Gen.Value TBM)},
      MachTB.wfLive m → retagTupleFieldsM m fnEntry vals fields = .ok (vals', m') →
      MachTB.wfLive m'
  | [], [], _, _, _, _, hwf, h => by
    unfold retagTupleFieldsM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | [], _ :: _, _, _, _, _, _, h => by unfold retagTupleFieldsM at h; cases h
  | _ :: _, [], _, _, _, _, _, h => by unfold retagTupleFieldsM at h; cases h
  | val :: vals, (_, ty) :: fields, _, _, _, _, hwf, h => by
    unfold retagTupleFieldsM at h
    obtain ⟨⟨_, m1⟩, hv, h⟩ := bind_ok h
    obtain ⟨⟨_, m2⟩, hvs, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact retagTupleFieldsM_tb_wfLive vals fields (retagValM_tb_wfLive val ty hwf hv) hvs

/-- `retagArrayElemsM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem retagArrayElemsM_tb_wfLive (elemTy : Gen.Type) :
    ∀ (vals : List (Gen.Value TBM)) {m m' : MachTB} {fnEntry : Bool}
      {vals' : List (Gen.Value TBM)},
      MachTB.wfLive m → retagArrayElemsM m fnEntry elemTy vals = .ok (vals', m') →
      MachTB.wfLive m'
  | [], _, _, _, _, hwf, h => by
    unfold retagArrayElemsM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | val :: vals, _, _, _, _, hwf, h => by
    unfold retagArrayElemsM at h
    obtain ⟨⟨_, m1⟩, hv, h⟩ := bind_ok h
    obtain ⟨⟨_, m2⟩, hvs, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact retagArrayElemsM_tb_wfLive elemTy vals (retagValM_tb_wfLive val elemTy hwf hv) hvs

end

/-- `evalStatementM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem evalStatementM_tb_wfLive {m m' : MachTB} {stmt : Gen.Statement}
    (hwf : MachTB.wfLive m) (h : evalStatementM m stmt = .ok m') :
    MachTB.wfLive m' := by
  cases stmt with
  | Assign dst src =>
    unfold evalStatementM at h
    obtain ⟨⟨⟨place, ty⟩, m1⟩, hp, h⟩ := bind_ok h
    obtain ⟨⟨⟨val, _⟩, m2⟩, hv, h⟩ := bind_ok h
    exact placeStoreM_tb_wfLive
      (evalValueM_tb_wfLive src (evalPlaceM_tb_wfLive dst hwf hp) hv) h
  | PlaceMention place =>
    unfold evalStatementM at h
    obtain ⟨⟨_, m1⟩, hp, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    exact evalPlaceM_tb_wfLive place hwf hp
  | Validate place fnEntry =>
    unfold evalStatementM at h
    obtain ⟨⟨⟨p, ty⟩, m1⟩, hp, h⟩ := bind_ok h
    obtain ⟨⟨val, m2⟩, hl, h⟩ := bind_ok h
    obtain ⟨⟨val', m3⟩, hr, h⟩ := bind_ok h
    exact placeStoreM_tb_wfLive
      (retagValM_tb_wfLive val ty
        (placeLoadM_tb_wfLive (evalPlaceM_tb_wfLive place hwf hp) hl) hr) h
  | StorageLive local_ =>
    unfold evalStatementM at h
    exact tryMutateCurFrameM_tb_wfLive (fun _ _ _ hfr => storageLiveM_tb_wfLive hwf hfr) h
  | StorageDead local_ =>
    unfold evalStatementM at h
    exact tryMutateCurFrameM_tb_wfLive (fun _ _ _ hfr => storageDeadM_tb_wfLive hwf hfr) h
  | Deinit place =>
    unfold evalStatementM at h
    obtain ⟨⟨⟨p, ty⟩, m1⟩, hp, h⟩ := bind_ok h
    dsimp only at h
    have hm1 := evalPlaceM_tb_wfLive place hwf hp
    cases hpa : p.aligned with
    | false => simp only [hpa, Bool.not_false, ↓reduceIte] at h; cases h
    | true =>
      simp only [hpa, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨cm, hd, h⟩ := bind_ok h
      obtain rfl := interp_pure_ok h
      exact cm_tb_deinit_wfLive hm1 hd
  | _ =>
    unfold evalStatementM at h; cases h

/-- `machineExitM` never returns normally (`Machine::exit` ends in
`throw_machine_stop!()` or a memory leak). -/
private theorem machineExitM_tb_ne_ok {α : Type} {m : MachTB} {x : α} :
    machineExitM (α := α) m ≠ .ok x := by
  intro h
  unfold machineExitM at h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h

/-- `loadRawDataM` on `MachTB` preserves `MachTB.wfLive`. -/
private theorem loadRawDataM_tb_wfLive {m m' : MachTB}
    {ptr : Gen.Pointer Gen.TreeBorrowsProvenance} {ptrTy : Gen.PtrType} {data : List UInt8}
    (hwf : MachTB.wfLive m) (h : loadRawDataM m ptr ptrTy = .ok (data, m')) :
    MachTB.wfLive m' := by
  unfold loadRawDataM at h
  split at h
  · split at h
    · obtain ⟨⟨bytes, cm⟩, hl, h⟩ := bind_ok h
      dsimp only at h
      split at h
      · obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
        exact cm_tb_load_wfLive hwf hl
      · cases h
    · cases h
  · cases h

/-- `prepareForInplacePassingM` on `MachTB` preserves `MachTB.wfLive`. -/
private theorem prepareForInplacePassingM_tb_wfLive {m m' : MachTB} {place : Gen.Place TBM}
    {ty : Gen.Type} (hwf : MachTB.wfLive m) (h : prepareForInplacePassingM m place ty = .ok m') :
    MachTB.wfLive m' := by
  unfold prepareForInplacePassingM at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨cm, hd, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  exact cm_tb_deinit_wfLive hwf hd

/-- `evalArgumentM` on `MachTB` preserves `MachTB.wfLive`. -/
private theorem evalArgumentM_tb_wfLive {m m' : MachTB} {arg : Gen.ArgumentExpr}
    {v : Gen.Value TBM × Gen.Type} (hwf : MachTB.wfLive m)
    (h : evalArgumentM m arg = .ok (v, m')) : MachTB.wfLive m' := by
  cases arg with
  | ByValue e =>
    unfold evalArgumentM at h
    exact evalValueM_tb_wfLive e hwf h
  | InPlace p =>
    unfold evalArgumentM at h
    obtain ⟨⟨⟨place, ty⟩, m1⟩, hp, h⟩ := bind_ok h
    obtain ⟨⟨val, m2⟩, hl, h⟩ := bind_ok h
    obtain ⟨m3, hprep, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact prepareForInplacePassingM_tb_wfLive
      (placeLoadM_tb_wfLive (evalPlaceM_tb_wfLive p hwf hp) hl) hprep

/-- `evalArgumentsM` on `MachTB` preserves `MachTB.wfLive`. -/
private theorem evalArgumentsM_tb_wfLive :
    ∀ (args : List Gen.ArgumentExpr) {m m' : MachTB} {vs : List (Gen.Value TBM × Gen.Type)},
      MachTB.wfLive m → evalArgumentsM m args = .ok (vs, m') → MachTB.wfLive m'
  | [], _, _, _, hwf, h => by
    unfold evalArgumentsM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | a :: as, _, _, _, hwf, h => by
    unfold evalArgumentsM at h
    obtain ⟨⟨_, m1⟩, ha, h⟩ := bind_ok h
    obtain ⟨⟨_, m2⟩, has, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact evalArgumentsM_tb_wfLive as (evalArgumentM_tb_wfLive hwf ha) has

/-- `allocFrameArgsM` on `TBM` preserves `TreeBorrowsMemory.wfLive`. -/
private theorem allocFrameArgsM_tb_wfLive :
    ∀ (ls : List Gen.LocalName) {fr fr' : Gen.StackFrame TBM} {cm cm' : Gen.ConcurrentMemory TBM},
      TreeBorrowsMemory.wfLive cm.memory →
      allocFrameArgsM fr cm ls = .ok (fr', cm') → TreeBorrowsMemory.wfLive cm'.memory
  | [], _, _, _, _, hwf, h => by
    unfold allocFrameArgsM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | l :: ls, _, _, _, _, hwf, h => by
    unfold allocFrameArgsM at h
    obtain ⟨⟨fr1, cm1⟩, hsl, h⟩ := bind_ok h
    exact allocFrameArgsM_tb_wfLive ls (storageLiveM_tb_wfLive hwf hsl) h

/-- `initFrameArgsM` on `MachTB` preserves `MachTB.wfLive`. -/
private theorem initFrameArgsM_tb_wfLive (frame : Gen.StackFrame TBM) :
    ∀ (ls : List Gen.LocalName) (args : List (Gen.Value TBM × Gen.Type)) {m m' : MachTB},
      MachTB.wfLive m → initFrameArgsM m frame ls args = .ok m' → MachTB.wfLive m'
  | [], _, _, _, hwf, h => by
    unfold initFrameArgsM at h
    obtain rfl := interp_pure_ok h
    exact hwf
  | _ :: _, [], _, _, hwf, h => by
    unfold initFrameArgsM at h
    obtain rfl := interp_pure_ok h
    exact hwf
  | l :: ls, (v, ty) :: args, m, _, hwf, h => by
    unfold initFrameArgsM at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨ok, _, h⟩ := bind_ok h
    split at h
    · cases h
    · obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨ptr, _, h⟩ := bind_ok h
      dsimp only at h
      split at h
      · rename_i m2 hst
        obtain ⟨m3, hm3, h⟩ := bind_ok h
        obtain rfl := interp_pure_ok hm3
        exact initFrameArgsM_tb_wfLive frame ls args (typedStoreM_tb_wfLive hwf hst) h
      all_goals
        obtain ⟨_, hbad, _⟩ := bind_ok h
        cases hbad

/-- `createFrameM` on `MachTB` preserves `MachTB.wfLive`. -/
private theorem createFrameM_tb_wfLive {m m' : MachTB} {func : Gen.Function}
    {spa : Gen.StackPopAction TBM} {conv : Gen.CallingConvention} {retTy : Gen.Type}
    {args : List (Gen.Value TBM × Gen.Type)} {fr : Gen.StackFrame TBM}
    (hwf : MachTB.wfLive m) (h : createFrameM m func spa conv retTy args = .ok (fr, m')) :
    MachTB.wfLive m' := by
  unfold createFrameM at h
  obtain ⟨⟨fr1, cm1⟩, hsl, h⟩ := bind_ok h
  obtain ⟨⟨fr2, cm2⟩, hal, h⟩ := bind_ok h
  dsimp only at h
  have hcm2 : TreeBorrowsMemory.wfLive cm2.memory :=
    allocFrameArgsM_tb_wfLive func.args (storageLiveM_tb_wfLive hwf hsl) hal
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    split at h
    · cases h
    · split at h
      · cases h
      · obtain ⟨m3, hinit, h⟩ := bind_ok h
        obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
        exact initFrameArgsM_tb_wfLive fr2 func.args args (m := { m with mem := cm2 }) hcm2 hinit

/-- `evalCallM` on `MachTB` preserves `MachTB.wfLive`. -/
private theorem evalCallM_tb_wfLive {m m' : MachTB} {callee : Gen.Function}
    {conv : Gen.CallingConvention} {args : List (Gen.Value TBM × Gen.Type)}
    {ret : Gen.Place TBM × Gen.Type} {nb ub' : Option Gen.BbName}
    (hwf : MachTB.wfLive m) (h : evalCallM m callee conv args ret nb ub' = .ok m') :
    MachTB.wfLive m' := by
  unfold evalCallM at h
  obtain ⟨⟨fr, m1⟩, hc, h⟩ := bind_ok h
  dsimp only at h
  have hm1 := createFrameM_tb_wfLive hwf hc
  unfold mutateCurStackM at h
  obtain ⟨⟨_, m2⟩, hs, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  obtain ⟨_, _, hs⟩ := bind_ok hs
  obtain ⟨_, hpure, hs⟩ := bind_ok hs
  obtain ⟨_, _, hs⟩ := bind_ok hs
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hs)
  exact hm1

/-- `evalIntrinsicM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem evalIntrinsicM_tb_wfLive {m m' : MachTB} {intrinsic : Gen.IntrinsicOp}
    {arguments : List (Gen.Value TBM × Gen.Type)} {retTy : Gen.Type} {val : Gen.Value TBM}
    (hwf : MachTB.wfLive m) (h : evalIntrinsicM m intrinsic arguments retTy = .ok (val, m')) :
    MachTB.wfLive m' := by
  cases intrinsic with
  | PointerExposeProvenance =>
    dsimp only [evalIntrinsicM] at h
    by_cases hlen : arguments.length = 1
    · simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte] at h
      rcases arguments with _ | ⟨⟨v, _⟩, _ | ⟨_, _⟩⟩
      · simp at hlen
      · rcases v with _ | _ | ⟨ptr, _ | _⟩ | _ | _
        · dsimp only [ub] at h; cases h
        · dsimp only [ub] at h; cases h
        · rcases retTy with ⟨_ | _, ⟨sz⟩⟩ | _ | _ | _ | _ | _ | _ | _
          · by_cases hsz : sz = 8
            · subst hsz
              dsimp only at h
              obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
              exact hwf
            · simp [hsz, ub] at h
          all_goals (dsimp only [ub] at h; cases h)
        all_goals (dsimp only [ub] at h; cases h)
      · simp at hlen
    · simp only [ne_eq, hlen, not_false_eq_true, ↓reduceIte, ub] at h; cases h
  | PointerWithExposedProvenance =>
    dsimp only [evalIntrinsicM] at h
    by_cases hlen : arguments.length = 1
    · simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte] at h
      rcases arguments with _ | ⟨⟨v, _⟩, _ | ⟨_, _⟩⟩
      · simp at hlen
      · rcases v with addr | _ | _ | _ | _
        · cases retTy with
          | Ptr retPtrTy =>
            dsimp only at h
            by_cases hmk : PtrType.meta_kind retPtrTy = .None
            · simp only [hmk, not_true_eq_false, ↓reduceIte] at h
              obtain ⟨_, _, h⟩ := bind_ok h
              obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
              exact hwf
            · simp only [hmk, not_false_eq_true, ↓reduceIte] at h
              dsimp only [ub] at h; cases h
          | _ => dsimp only [ub] at h; cases h
        all_goals (dsimp only [ub] at h; cases h)
      · simp at hlen
    · simp only [ne_eq, hlen, not_false_eq_true, ↓reduceIte, ub] at h; cases h
  | Exit =>
    dsimp only [evalIntrinsicM] at h
    exact absurd h machineExitM_tb_ne_ok
  | Abort =>
    dsimp only [evalIntrinsicM, abort] at h; cases h
  | Assume =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h); exact hwf)
      | (dsimp only [ub] at h; cases h)
  | PrintStdout =>
    dsimp only [evalIntrinsicM] at h
    split at h
    · obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
      exact hwf
    · dsimp only [ub] at h; cases h
  | PrintStderr =>
    dsimp only [evalIntrinsicM] at h
    split at h
    · obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
      exact hwf
    · dsimp only [ub] at h; cases h
  | Allocate =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨⟨_, cm⟩, ha, h⟩ := bind_ok h
         obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
         exact cm_tb_allocate_wfLive hwf ha)
  | Deallocate =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨cm, hd, h⟩ := bind_ok h
         obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
         exact cm_tb_deallocate_wfLive hwf hd)
  | RawEq =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨⟨_, m1⟩, hl1, h⟩ := bind_ok h
         obtain ⟨⟨_, m2⟩, hl2, h⟩ := bind_ok h
         obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
         exact loadRawDataM_tb_wfLive (loadRawDataM_tb_wfLive hwf hl1) hl2)
  | GetUnwindPayload =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨_, _, h⟩ := bind_ok h
         repeat' split at h
         all_goals first
           | (obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h); exact hwf)
           | (dsimp only [ub] at h; cases h))
  | _ =>
    dsimp only [evalIntrinsicM, unsupported] at h; cases h

/-- `evalArgsM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem evalArgsM_tb_wfLive :
    ∀ (es : List Gen.ValueExpr) {m m' : MachTB} {args : List (Gen.Value TBM × Gen.Type)},
      MachTB.wfLive m → evalArgsM m es = .ok (args, m') → MachTB.wfLive m'
  | [], _, _, _, hwf, h => by
    unfold evalArgsM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | e :: es, _, _, _, hwf, h => by
    unfold evalArgsM at h
    obtain ⟨⟨_, m1⟩, he, h⟩ := bind_ok h
    obtain ⟨⟨_, m2⟩, hes, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact evalArgsM_tb_wfLive es (evalValueM_tb_wfLive e hwf he) hes

/-- `deallocAllM` on `TBM` preserves `TreeBorrowsMemory.wfLive`. -/
theorem deallocAllM_tb_wfLive :
    ∀ (fuel : Nat) {fr fr' : Gen.StackFrame TBM} {cm cm' : Gen.ConcurrentMemory TBM},
      TreeBorrowsMemory.wfLive cm.memory →
      deallocAllM fuel fr cm = .ok (fr', cm') →
      TreeBorrowsMemory.wfLive cm'.memory
  | 0, fr, _, _, _, hwf, h => by
    unfold deallocAllM at h
    rcases hent : fr.locals.entries with _ | ⟨⟨_, _⟩, _⟩ <;> simp only [hent] at h
    · obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h); exact hwf
    · cases h
  | fuel + 1, fr, _, _, _, hwf, h => by
    unfold deallocAllM at h
    rcases hent : fr.locals.entries with _ | ⟨⟨local_, _⟩, _⟩ <;> simp only [hent] at h
    · obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h); exact hwf
    · obtain ⟨⟨fr1, cm1⟩, hsd, h⟩ := bind_ok h
      exact deallocAllM_tb_wfLive fuel (storageDeadM_tb_wfLive hwf hsd) h

/-- `evalReturnM` on `MachTB` preserves `MachTB.wfLive` across return-value
loading, local teardown (`deallocAllM`), and frame protector release (`end_call`). -/
theorem evalReturnM_tb_wfLive {m m' : MachTB}
    (hwf : MachTB.wfLive m) (h : evalReturnM m = .ok m') :
    MachTB.wfLive m' := by
  unfold evalReturnM at h
  obtain ⟨t, _, h⟩ := bind_ok h
  dsimp only at h
  cases hlast : t.stack.getLast? with
  | none => simp only [hlast] at h; cases h
  | some f =>
    simp only [hlast] at h
    obtain ⟨frame, hfr, h⟩ := bind_ok h
    cases interp_pure_ok hfr
    obtain ⟨threads, _, h⟩ := bind_ok h
    obtain ⟨calleeTy, _, h⟩ := bind_ok h
    obtain ⟨lay, _, h⟩ := bind_ok h
    obtain ⟨align, _, h⟩ := bind_ok h
    obtain ⟨retPtr, _, h⟩ := bind_ok h
    obtain ⟨⟨retVal, m1⟩, hload, h⟩ := bind_ok h
    have hm1 := typedLoadM_tb_wfLive (m := { m with threads := threads }) hwf hload
    obtain ⟨⟨frame1, cm1⟩, hdealloc, h⟩ := bind_ok h
    dsimp only at h
    have hcm1 := deallocAllM_tb_wfLive f.locals.entries.length hm1 hdealloc
    obtain ⟨cm2, hend, h⟩ := bind_ok h
    have hcm2 : MachTB.wfLive { m1 with mem := cm2 } := cm_tb_end_call_wfLive hcm1 hend
    cases hspa : frame1.stack_pop_action with
    | BottomOfStack =>
      simp only [hspa] at h
      exact terminateActiveThreadM_tb_wfLive hcm2 h
    | BackToCaller nextBlock _ callerRetPtr =>
      simp only [hspa] at h
      obtain ⟨t2, _, h⟩ := bind_ok h
      by_cases hst : t2.stack.length = 0
      · simp only [hst, ↓reduceIte] at h; cases h
      · simp only [hst, ↓reduceIte] at h
        obtain ⟨m2, hstore, h⟩ := bind_ok h
        have hm2 := typedStoreM_tb_wfLive hcm2 hstore
        cases nextBlock with
        | none => cases h
        | some nb => exact jumpToBlockM_tb_wfLive hm2 h

/-- `evalTerminatorM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem evalTerminatorM_tb_wfLive {m m' : MachTB} {term : Gen.Terminator}
    (hwf : MachTB.wfLive m) (h : evalTerminatorM m term = .ok m') :
    MachTB.wfLive m' := by
  cases term with
  | Goto blockName => exact jumpToBlockM_tb_wfLive hwf h
  | Switch value cases fallback =>
    unfold evalTerminatorM at h
    obtain ⟨⟨⟨v, _⟩, m1⟩, hv, h⟩ := bind_ok h
    dsimp only at h
    have hm1 := evalValueM_tb_wfLive value hwf hv
    cases v with
    | Int i => exact jumpToBlockM_tb_wfLive hm1 h
    | _ => cases h
  | Unreachable => unfold evalTerminatorM at h; cases h
  | Call callee conv arguments retExpr nextBlock unwindBlock =>
    unfold evalTerminatorM at h
    obtain ⟨⟨⟨retPlace, retTy⟩, m1⟩, hp, h⟩ := bind_ok h
    obtain ⟨m2, hprep, h⟩ := bind_ok h
    obtain ⟨⟨⟨calleeVal, _⟩, m3⟩, hv, h⟩ := bind_ok h
    obtain ⟨calleeFn, _, h⟩ := bind_ok h
    obtain ⟨⟨args, m4⟩, hargs, h⟩ := bind_ok h
    exact evalCallM_tb_wfLive
      (evalArgumentsM_tb_wfLive arguments
        (evalValueM_tb_wfLive callee
          (prepareForInplacePassingM_tb_wfLive (evalPlaceM_tb_wfLive retExpr hwf hp) hprep) hv)
        hargs) h
  | Return => exact evalReturnM_tb_wfLive hwf h
  | Intrinsic intrinsic arguments retExpr nextBlock =>
    unfold evalTerminatorM at h
    obtain ⟨⟨⟨retPlace, retTy⟩, m1⟩, hp, h⟩ := bind_ok h
    obtain ⟨⟨args, m2⟩, ha, h⟩ := bind_ok h
    obtain ⟨⟨val, m3⟩, hi, h⟩ := bind_ok h
    obtain ⟨m4, hs, h⟩ := bind_ok h
    have hm4 := placeStoreM_tb_wfLive
      (evalIntrinsicM_tb_wfLive
        (evalArgsM_tb_wfLive arguments (evalPlaceM_tb_wfLive retExpr hwf hp) ha) hi) hs
    cases nextBlock with
    | none => cases h
    | some nb => exact jumpToBlockM_tb_wfLive hm4 h
  | _ => unfold evalTerminatorM at h; cases h

/-- Every single step of `MachTB` (`stepTB`) preserves `MachTB.wfLive`. -/
theorem stepTB_wfLive {m m' : MachTB}
    (hwf : MachTB.wfLive m) (h : stepTB m = .ok m') :
    MachTB.wfLive m' := by
  unfold stepTB stepM at h
  cases hany : m.threads.any (fun t => decide (t.state = .Enabled)) with
  | false => simp only [hany, Bool.not_false, ↓reduceIte] at h; cases h
  | true =>
    simp only [hany, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    dsimp only [resetDataRaceTrackingM] at h
    obtain ⟨tid, _, h⟩ := bind_ok h
    obtain ⟨frame, _, h⟩ := bind_ok h
    obtain ⟨block, _, h⟩ := bind_ok h
    have hm0 : MachTB.wfLive
        { { m with mem := { m.mem with accesses := [] } } with active_thread := tid } := hwf
    by_cases hns : frame.next_stmt = (block.statements.length : Int)
    · simp only [hns, ↓reduceIte] at h
      obtain ⟨m2, hterm, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain rfl := interp_pure_ok h
      exact evalTerminatorM_tb_wfLive hm0 hterm
    · simp only [hns, ↓reduceIte] at h
      obtain ⟨stmt, _, h⟩ := bind_ok h
      obtain ⟨m1, hev, h⟩ := bind_ok h
      obtain ⟨m2, hmut, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain rfl := interp_pure_ok h
      exact mutateCurFrameM_tb_wfLive (evalStatementM_tb_wfLive hm0 hev) hmut

/-- Arbitrary multi-step execution of `MachTB` (`stepsTB n`) preserves
`MachTB.wfLive` across every `n : Nat` (statements, reborrows, `Validate`/`Retag`,
`StorageLive`/`StorageDead`, `Box` deallocations, loops, and `Return`/`end_call`). -/
theorem stepsTB_wfLive :
    ∀ {n : Nat} {m m' : MachTB},
      MachTB.wfLive m → stepsTB n m = .ok m' → MachTB.wfLive m'
  | 0, _, _, hwf, h => by
    unfold stepsTB stepsM at h
    obtain rfl := interp_pure_ok h
    exact hwf
  | _ + 1, _, _, hwf, h => by
    unfold stepsTB stepsM at h
    obtain ⟨m1, hs, h⟩ := bind_ok h
    exact stepsTB_wfLive (stepTB_wfLive hwf hs) h

end MiniRustSpec.Correspondence
