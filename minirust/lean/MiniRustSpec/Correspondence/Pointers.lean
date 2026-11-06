/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Run

/-!
# Raw pointers in both semantics (MR-3.1)

This module collects what both semantics do with raw pointers, as the
foundation for extending the correspondence (`step_correspondence`) to
`&raw const` / `&raw mut`, `*p`, `Offset`, and pointer casts:

* **MiniRust's representation of thin pointers.** `ptrBytes addr prov` is the
  encoding `encode_ptr` produces for an address in `[0, 2^64)`: the eight
  little-endian address bytes, each carrying the fragment of the pointer's
  provenance at its own position. `decode_ptr` reads the pointer back, and
  `check_value` accepts it at every thin raw pointer type
  (`decode_thinRawPtr`, `encode_thinRawPtr`, `checkValue_thinRawPtr`).
  A byte whose fragment belongs to another provenance makes the decoded
  pointer lose its provenance (`decodePtrProvenance_mixed`).
* **Anneal's model of raw pointers.** `&raw const p` and `&raw mut p` push a
  fresh Tree Borrows entry and return a pointer whose `allocId` is the entry's
  tag (`evalRvalue_rawPtr_local`); a dereference reads or writes the entry's
  target local at the entry's projection and ignores the pointer's
  `offsetBytes` (`evalOperand_copy_deref`, `writePlaceValue_deref_root`);
  `Offset(p, n)` adds the raw count `n` to `offsetBytes` without scaling it by
  the pointee size and without any bounds check (`evalRvalue_offset`); and
  `PointerExposeProvenance` returns `tag * 65536 + offsetBytes`
  (`evalRvalue_expose`).

The two models agree on creating a raw pointer to a local, an array element,
or a struct field, on reading and writing through it, on `PtrToPtr` casts, and
on rejecting reads through dangling pointers. They disagree, with MiniRust as
the ground truth, on:

1. **Dereferencing an offset pointer**: Anneal reads the original target,
   MiniRust the offset address, or raises UB if that address is misaligned
   for the pointee type or outside the allocation.
2. **Out-of-bounds and overflowing `Offset`**: MiniRust's `ptr_offset_inbounds`
   (after `MulUnchecked`) raises UB; Anneal continues.
3. **Exposed addresses**: Anneal's address encodes the borrow tag, so two raw
   pointers to the same local expose different integers; MiniRust exposes the
   allocation's address.
4. **Aliasing**: Anneal's Tree Borrows entries make a write through a
   `&raw const` pointer, or an access through a pointer disabled by a direct
   write to its target, UB; `BasicMemory` has no aliasing model and accepts
   both.

In 1-3 Anneal's semantics accepts executions that MiniRust rejects or runs
differently, so a correspondence covering them would be false; in 4 Anneal is
merely stricter. `MiniRustSpec.Correspondence.PointerWitness` checks each case
on concrete programs in both semantics.
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

/-- The bytes `encode_ptr` produces for the thin pointer `⟨addr, prov⟩` with
`addr < 2^64` (`encodePtr_eq`). -/
def ptrBytes (addr : Nat) (prov : Option Prov) : List Byte :=
  encodePtrBytes prov 0 (leBytes addr 8)

theorem encodePtrBytes_length (prov : Option Prov) (i : Nat) (data : List UInt8) :
    (encodePtrBytes prov i data).length = data.length := by
  induction data generalizing i with
  | nil => rfl
  | cons b rest ih => simp [encodePtrBytes, ih]

theorem ptrBytes_length (addr : Nat) (prov : Option Prov) : (ptrBytes addr prov).length = 8 := by
  simp [ptrBytes, encodePtrBytes_length, leBytes_length]

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

theorem checkValue_thinRawPtr (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) :
    checkValue (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })
      thinRawPtrTy = .ok () := by
  have hlt := lt_two_pow_64_int h
  have hin : inBounds (addr : Int) .Unsigned x86_64.PTR_SIZE = true := by
    rw [inBounds_usize]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  simp [thinRawPtrTy, checkValue, checkPtr, hin, ensureElseUb, checkPtrMetadata,
    PtrType.meta_kind, PtrType.safe_pointee]

/-- An address outside `[0, 2^64)` is not a valid raw pointer
(`Value::Ptr: pointer out-of-bounds`). -/
theorem checkValue_thinRawPtr_oob (addr : Int) (h : ¬ (0 ≤ addr ∧ addr < 18446744073709551616))
    (prov : Option Prov) :
    checkValue (.Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none })
      thinRawPtrTy = .error (.ub "Value::Ptr: pointer out-of-bounds") := by
  have hin : inBounds addr .Unsigned x86_64.PTR_SIZE = false := by
    rw [inBounds_usize]
    by_cases h0 : 0 ≤ addr
    · have : ¬ addr < 18446744073709551616 := fun h' => h ⟨h0, h'⟩
      simp [h0, this]
    · simp [h0]
  simp [thinRawPtrTy, checkValue, checkPtr, hin, ensureElseUb, ub]

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

/-- Anneal's `&raw const place` / `&raw mut place` on a live local: a fresh tag
`nextTag` names a new Tree Borrows entry for the place, and the resulting
pointer is that tag at offset `0`. The place is not evaluated any further: an
out-of-bounds `ConstantIndex` (or a field that does not exist) is accepted
here and only faults when the pointer is dereferenced, whereas MiniRust's
`AddrOf` evaluates the place and raises UB immediately. -/
theorem evalRvalue_rawPtr_local (locals : List LocalSlot) (mutbl : MirAst.Mutability) (place : Place)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
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
      cases mutbl <;> simp [evalRvalue, get?, hs, rawPtrEntry, rawPtrPerm]
    | init v =>
      cases mutbl <;> simp [evalRvalue, get?, hs, rawPtrEntry, rawPtrPerm]
  | cons e rest =>
    cases e with
    | deref => exact absurd rfl (hnd rest)
    | _ =>
      cases slot with
      | dead => exact absurd rfl hlive
      | uninit => cases mutbl <;> simp_all [evalRvalue, get?, rawPtrEntry, rawPtrPerm]
      | init v => cases mutbl <;> simp_all [evalRvalue, get?, rawPtrEntry, rawPtrPerm]

/-- Anneal's read of `copy (*p).rest` when `p` holds a pointer whose tag names
a usable (not `Disabled`) entry with an initialized target: the target's value
at the entry's projection followed by `rest`. The pointer's `offsetBytes` does
not occur in the statement: a dereference reads the entry's place no matter
how far the pointer has been offset. -/
theorem evalOperand_copy_deref (locals : List LocalSlot) (p : Nat) (rest : List ProjectionElem)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (layouts : Layout.LayoutTable) (callerLocals : List LocalSlot)
    (ptrVal : ProvenancePtr) (sz : Nat) (hp : locals[p]? = some (.init (.ptr ptrVal sz)))
    (entry : BorrowEntry) (he : lookupBorrow borrows ptrVal.tag = some entry)
    (hperm : entry.perm ≠ .disabled)
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
    rw [htp] at hr
    simp only [appendProjections] at hr
    cases hpe : entry.perm with
    | disabled => exact absurd hpe hperm
    | _ => simp [evalOperand, get?, hp, he, hpe, ht, htp, hr]

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

/-- Anneal's write `(*p) = val` through an `Active` entry whose target is the
whole local `entry.targetLocal` (no projection): the target local now holds
`val`, wherever the pointer points. -/
theorem writePlaceValue_deref_root (locals : List LocalSlot) (borrows : List BorrowEntry)
    (p : Nat) (val : Value) (ptrVal : ProvenancePtr) (sz : Nat)
    (hp : locals[p]? = some (.init (.ptr ptrVal sz))) (entry : BorrowEntry)
    (he : lookupBorrow borrows ptrVal.tag = some entry) (hperm : entry.perm = .active)
    (hproj : entry.targetProjection = []) (slot : LocalSlot)
    (ht : locals[entry.targetLocal]? = some slot) (hlive : slot ≠ .dead) :
    writePlaceValue locals borrows ⟨p, [.deref]⟩ val =
      .ok (locals.set entry.targetLocal (.init val)) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp ht
  cases slot with
  | dead => exact absurd rfl hlive
  | uninit => simp [writePlaceValue, get?, hp, he, hperm, hproj, set?, hlt, hget]
  | init v => simp [writePlaceValue, get?, hp, he, hperm, hproj, set?, hlt, hget]

/-- Anneal's `Offset(p, n)`: the raw count `n` (not scaled by the pointee
size) is added to the pointer's `offsetBytes`, for every `n` and without any
bounds check. MiniRust (through `minimize`) offsets by `n * size_of::<T>()`
bytes with `ptr_offset_inbounds`, which raises UB when the byte range leaves
the pointer's allocation, and `MulUnchecked` raises UB when `n *
size_of::<T>()` overflows. -/
theorem evalRvalue_offset (locals : List LocalSlot) (l r : Operand) (mem : MirSemantics.Memory)
    (decls : List LocalDecl) (layouts : Layout.LayoutTable) (ptrVal : ProvenancePtr) (sz : Nat)
    (locals₁ : List LocalSlot)
    (hl : evalOperand locals l mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr ptrVal sz) locals₁)
    (sc : ScalarInt) (locals₂ : List LocalSlot)
    (hr : evalOperand locals₁ r mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar sc) locals₂) :
    evalRvalue locals (.binaryOp .offset l r) mem decls layouts =
      .ok (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + sc.bits } sz) locals₂ mem := by
  simp [evalRvalue, hl, hr]

/-- Anneal's `PtrToPtr` cast keeps the pointer, tag and offset included;
`minimize` translates a cast between thin raw pointers to its operand. -/
theorem evalRvalue_ptrToPtr (locals : List LocalSlot) (op : Operand) (ty : Ty)
    (mem : MirSemantics.Memory) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (ptrVal : ProvenancePtr) (sz : Nat) (locals' : List LocalSlot)
    (h : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.ptr ptrVal sz) locals') :
    evalRvalue locals (.cast .ptrToPtr op ty) mem decls layouts = .ok (.ptr ptrVal sz) locals' mem := by
  simp [evalRvalue, h]

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

end MiniRustSpec.Correspondence
