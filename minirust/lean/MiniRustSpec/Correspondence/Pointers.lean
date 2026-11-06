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

/-! ## MiniRust: thin-pointer loads, stores, and zero-offset arithmetic -/

theorem decode_thinRawPtr_uninit : Type.decode thinRawPtrTy (uninitBytes usizeIt) = .ok none := rfl

theorem typedLoad_of_ok {m : Mach} {ptr : Ptr} {ty : Gen.Type} {sz : Size} {al : Align}
    {align : Align} {bytes : List Byte} {cm : Gen.ConcurrentMemory BM} {val : Val}
    (hlay : Type.layout ty = .ok (.Sized sz al))
    (hload : CM.load m.mem ptr sz align .None = .ok (bytes, cm))
    (hdec : Type.decode ty bytes = .ok (some val))
    (hck : checkValue val ty = .ok ()) :
    typedLoad m ptr ty align .None = .ok (val, { m with mem := cm }) := by
  simp only [typedLoad, hlay, expect_size_sized, ok_bind, hload, hdec, hck, pure_ok]

theorem typedStore_of_ok {m : Mach} {ptr : Ptr} {val : Val} {ty : Gen.Type}
    {align : Align} {bytes : List Byte} {cm : Gen.ConcurrentMemory BM}
    (hck : checkValue val ty = .ok ())
    (henc : Type.encode ty val = .ok bytes)
    (hstore : CM.store m.mem ptr bytes align .None = .ok cm) :
    typedStore m ptr val ty align .None = .ok { m with mem := cm } := by
  simp only [typedStore, hck, ok_bind, pure_ok, henc, hstore]

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

theorem retagPtrBM_shape {m : Mach} {ctx : Ctx} {f1 f2 : Frame} {rest : List Frame}
    {A : List Gen.Allocation} (h : Shape m ctx (f1 :: f2 :: rest) A) (ptr : Gen.Pointer Prov) :
    retagPtrBM m ptr = .ok ptr := by
  simp [retagPtrBM, listIndex, h.threads, h.active, thread1]

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
  cases MirSemantics.stripTransparentProjections proj <;> rfl

theorem appendProjections_nil_right (l : List ProjectionElem) :
    appendProjections l [] = l := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [appendProjections, ih]

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

theorem invalidateDerefWriteBorrows_noop (locals : List LocalSlot) (borrows : List BorrowEntry)
    (p : Nat) (ptrVal : ProvenancePtr) (entry : BorrowEntry)
    (hp : locals[p]? = some (.init (.ptr ptrVal 8)))
    (he : lookupBorrow borrows ptrVal.tag = some entry)
    (hrlen : entry.rangeLen = 0) (hroff : entry.rangeOffset = 0)
    (hdisj : ∀ e ∈ borrows, e.targetLocal = entry.targetLocal →
      (e.tag = ptrVal.tag ∧ e.perm ≠ .reserved) ∨
      (e.tag ≠ ptrVal.tag ∧
        MirSemantics.projectionsOverlap e.targetProjection entry.targetProjection = false)) :
    invalidateDerefWriteBorrows locals borrows ⟨p, [.deref]⟩ [] = borrows := by
  have happ := appendProjections_nil_right entry.targetProjection
  unfold invalidateDerefWriteBorrows
  simp only [get?, hp, he, happ]
  cases htp : entry.targetProjection with
  | nil =>
    have hrl : Nat.beq entry.rangeLen 0 = true := by simp [hrlen]
    simp only [hrl]
    apply invalidateConflictingBorrows_self
    intro e he_mem hloc
    rcases hdisj e he_mem hloc with hself | ⟨_, hov⟩
    · exact hself
    · rw [htp, projectionsOverlap_nil_right] at hov
      cases hov
  | cons ph pt =>
    rw [hroff, hrlen]
    apply invalidateConflictingBorrowsAtProj_self_or_disjoint
    intro e he_mem hloc
    rw [← htp]
    exact hdisj e he_mem hloc

theorem writePlaceValue_deref_proj (locals : List LocalSlot) (borrows : List BorrowEntry)
    (p : Nat) (val : Value) (ptrVal : ProvenancePtr)
    (hp : locals[p]? = some (.init (.ptr ptrVal 8))) (entry : BorrowEntry)
    (he : lookupBorrow borrows ptrVal.tag = some entry) (hperm : entry.perm = .active)
    (ph : ProjectionElem) (pt : List ProjectionElem)
    (hproj : entry.targetProjection = ph :: pt)
    (rootVal rootVal' : Value) (ht : locals[entry.targetLocal]? = some (.init rootVal))
    (hw : writeProjectedValue locals rootVal (ph :: pt) val = .ok rootVal') :
    writePlaceValue locals borrows ⟨p, [.deref]⟩ val =
      .ok (locals.set entry.targetLocal (.init rootVal')) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp ht
  have happ := appendProjections_nil_right pt
  simp [writePlaceValue, get?, hp, he, hperm, hproj, happ, hget, hw, set?, hlt]

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
    ((bodyMutAddrTakenLocals body).isEmpty = true ∨
      ((∀ bb ∈ body.basicBlocks, 0 ∉ termTargets bb.terminator) ∧
        match body.basicBlocks with
        | [] => True
        | bb0 :: restBbs =>
          rawPtrListDisjoint (bodyMutAddrTakenLocals body) bb0.statements = true ∧
          ∀ bb ∈ restBbs, noMutAddrOfInStmts (bodyMutAddrTakenLocals body) bb.statements = true)) := by
  unfold ptrAliasingOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem] at h
  rcases h with ⟨⟨h1, h2⟩, h3⟩
  refine ⟨h1, h2, ?_⟩
  rcases h3 with hemp | ⟨hno0, hbbs⟩
  · exact .inl hemp
  · right
    refine ⟨hno0, ?_⟩
    cases hbb_eq : body.basicBlocks with
    | nil => trivial
    | cons bb0 restBbs =>
      rw [hbb_eq] at hbbs
      simpa [Bool.and_eq_true, List.all_eq_true] using hbbs

theorem mem_bodyAddrTakenLocals {body : CapturedMir} {bb : BasicBlockData} {st : MirAst.Statement}
    {dst : Place} {mutbl : MirAst.Mutability} {q : Place}
    (hbb : bb ∈ body.basicBlocks) (hst : st ∈ bb.statements)
    (hkind : st.kind = .assign dst (.rawPtr mutbl q)) :
    q.local_ ∈ bodyAddrTakenLocals body := by
  unfold bodyAddrTakenLocals
  rw [List.mem_flatMap]
  refine ⟨bb, hbb, List.mem_filterMap.mpr ⟨st, hst, ?_⟩⟩
  simp [hkind]

theorem mem_bodyMutAddrTakenLocals {body : CapturedMir} {bb : BasicBlockData} {st : MirAst.Statement}
    {dst : Place} {q : Place}
    (hbb : bb ∈ body.basicBlocks) (hst : st ∈ bb.statements)
    (hkind : st.kind = .assign dst (.rawPtr .mut q)) :
    q.local_ ∈ bodyMutAddrTakenLocals body := by
  unfold bodyMutAddrTakenLocals
  rw [List.mem_flatMap]
  refine ⟨bb, hbb, List.mem_filterMap.mpr ⟨st, hst, ?_⟩⟩
  simp [hkind]

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

theorem rawPtrListDisjoint_lt {mutLocals : List Nat} {stmts : List MirAst.Statement}
    (hdisj : rawPtrListDisjoint mutLocals stmts = true)
    {i j : Nat} (hlt : i < j) {si sj : MirAst.Statement}
    (hi : stmts[i]? = some si) (hj : stmts[j]? = some sj)
    {dst1 dst2 : Place} {m1 m2 : MirAst.Mutability} {k : Nat}
    {projs1 projs2 : List ProjectionElem}
    (hki : si.kind = .assign dst1 (.rawPtr m1 ⟨k, projs1⟩))
    (hkj : sj.kind = .assign dst2 (.rawPtr m2 ⟨k, projs2⟩))
    (hmut : k ∈ mutLocals) :
    MirSemantics.projectionsOverlap projs1 projs2 = false ∧
    MirSemantics.projectionsOverlap projs2 projs1 = false := by
  induction stmts generalizing i j with
  | nil => simp at hi
  | cons s rest ih =>
    simp only [rawPtrListDisjoint, Bool.and_eq_true] at hdisj
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        simp at hi hj
        subst hi
        have hsj_mem : sj ∈ rest := List.mem_of_getElem? hj
        have h1 := hdisj.1
        have hcont : mutLocals.contains k = true := List.contains_iff_mem.mpr hmut
        simp only [hki, hcont, ↓reduceIte, List.all_eq_true] at h1
        have hpair := h1 sj hsj_mem
        simp only [hkj, ne_eq, not_true_eq_false, decide_false, Bool.false_or,
          Bool.and_eq_true, Bool.not_eq_true'] at hpair
        exact hpair
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        rw [List.getElem?_cons_succ] at hi hj
        exact ih hdisj.2 (by omega) hi hj

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

/-- Synchronized borrow-table and raw-pointer local invariant for `StateRelN`. -/
structure BorrowsOk (body : CapturedMir) (ctx : Ctx) (view : List LocalSlot)
    (s : MachineState) (lm : Map Gen.LocalName Ptr) : Prop where
  tags_lt : ∀ e ∈ s.memory.borrows, e.tag < s.memory.nextTag
  entries_ok : ∀ e ∈ s.memory.borrows, ∃ (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType) (relOff : Nat),
    e = rawPtrEntry e.tag mutbl ⟨e.targetLocal, e.targetProjection⟩ ∧
    e.targetLocal ∈ bodyAddrTakenLocals body ∧
    (mutbl = .mut → e.targetLocal ∈ bodyMutAddrTakenLocals body) ∧
    ptrTargetSpec body.layouts body.localDecls ⟨e.targetLocal, e.targetProjection⟩ = some (pointeeIt, relOff)
  target_ptrs : inFragment body = true → ∀ k ∈ bodyAddrTakenLocals body,
    view[k]? ≠ some .dead ∧
    mapGet lm (localName k) = some (localPtr ctx k) ∧
    (∀ d, body.localDecls[k]? = some d →
      isPtrTy d.ty = false ∧
      AddrOk (ctx.addrs.getD k 0) (itOf d body.layouts) ∧
      ctx.addrs.getD k 0 + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 64)
  mut_disjoint : ∀ e1 ∈ s.memory.borrows, ∀ e2 ∈ s.memory.borrows,
    e1.tag ≠ e2.tag → e1.targetLocal = e2.targetLocal →
    e1.targetLocal ∈ bodyMutAddrTakenLocals body →
    MirSemantics.projectionsOverlap e1.targetProjection e2.targetProjection = false
  mut_pc_ok : ∀ k ∈ bodyMutAddrTakenLocals body,
    (s.frame.blockIdx = 0 ∧ ∀ bb0, body.basicBlocks[0]? = some bb0 →
      ∀ e ∈ s.memory.borrows, e.targetLocal = k →
        ∃ idx < s.frame.stmtIdx, ∃ st dst mutbl,
          bb0.statements[idx]? = some st ∧
          st.kind = .assign dst (.rawPtr mutbl ⟨k, e.targetProjection⟩)) ∨
    s.frame.blockIdx ≠ 0
  ptr_slots : ∀ (p : Nat) (dp : LocalDecl) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
      (ptrVal : ProvenancePtr),
    body.localDecls[p]? = some dp →
    ptrPointeeOf dp.ty = some (mutbl, pointeeIt) →
    view[p]? = some (.init (.ptr ptrVal 8)) →
    ∃ (entry : BorrowEntry) (relOff : Nat),
      ptrVal.offsetBytes = 0 ∧
      lookupBorrow s.memory.borrows ptrVal.tag = some entry ∧
      (mutbl = .mut → entry.perm = .active) ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (pointeeIt, relOff)

theorem BorrowsOk.target_ne_of_not_addrTaken {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm) {i : Nat} (hi : i ∉ bodyAddrTakenLocals body) :
    ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i := by
  intro e he heq
  obtain ⟨_, _, _, _, hmem, _, _⟩ := hb.entries_ok e he
  exact hi (heq ▸ hmem)

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
  mut_disjoint e1 he1 := by simp [hbor] at he1
  mut_pc_ok k _ := by
    by_cases hb0 : s.frame.blockIdx = 0
    · exact .inl ⟨hb0, fun _ _ e he => by simp [hbor] at he⟩
    · exact .inr hb0
  ptr_slots p dp mutbl pointeeIt ptrVal hdp hp hv := by
    have hp_ty : isPtrTy dp.ty = true := by simp [isPtrTy, hp]
    exact False.elim (hnoPtr p dp ptrVal hdp hp_ty hv)

theorem BorrowsOk.advance_keep {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {locals' : List LocalSlot} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm) :
    BorrowsOk body ctx view (advanceStmt s locals' s.memory) lm where
  tags_lt := hb.tags_lt
  entries_ok := hb.entries_ok
  target_ptrs := hb.target_ptrs
  mut_disjoint := hb.mut_disjoint
  mut_pc_ok k hk := by
    rcases hb.mut_pc_ok k hk with ⟨hb0, hstmts⟩ | hne0
    · refine .inl ⟨hb0, fun bb0 hbb0 e he hke => ?_⟩
      obtain ⟨idx, hlt, st, dst, mutbl, hst, hkind⟩ := hstmts bb0 hbb0 e he hke
      exact ⟨idx, by simp [advanceStmt]; omega, st, dst, mutbl, hst, hkind⟩
    · exact .inr hne0
  ptr_slots := hb.ptr_slots

theorem BorrowsOk.advance_set_nonptr {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {locals' : List LocalSlot} {lm' : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm')
    (i : Nat) (slot' : LocalSlot)
    (hdead : i ∈ bodyAddrTakenLocals body → slot' ≠ .dead)
    (hnp : ∀ dp pv, body.localDecls[i]? = some dp → isPtrTy dp.ty = true →
      slot' ≠ .init (.ptr pv 8)) :
    BorrowsOk body ctx (view.set i slot') (advanceStmt s locals' s.memory) lm' := by
  have hb' := hb.advance_keep (locals' := locals')
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
    mut_disjoint := hb'.mut_disjoint
    mut_pc_ok := hb'.mut_pc_ok
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
    (target : Nat) (htgt : target ∈ termTargets bb.terminator)
    (locals' : List LocalSlot) :
    BorrowsOk body ctx view (jumpState s target locals') lm :=
  { tags_lt := hb.tags_lt
    entries_ok := hb.entries_ok
    target_ptrs := hb.target_ptrs
    mut_disjoint := hb.mut_disjoint
    mut_pc_ok := fun k hk => by
      obtain ⟨_, _, hmut⟩ := ptrAliasingOk_spec hpa
      rcases hmut with hemp | ⟨hno0, _⟩
      · rw [List.isEmpty_iff] at hemp
        rw [hemp] at hk; simp at hk
      · have hne0 : target ≠ 0 := fun h0 =>
          hno0 bb (List.mem_of_getElem? hbb) (h0 ▸ htgt)
        exact .inr hne0
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
            cases m <;> simp [rvalueOk]
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
    | _ => simp at hkind
  | _ => simp at hkind

theorem derefPointeeTy_of_ptrPointeeOf {t : MirAst.Ty} {mutbl : MirAst.Mutability}
    {it : Gen.IntType} (h : ptrPointeeOf t = some (mutbl, it)) :
    derefPointeeTy t = some (.Int it) := by
  unfold ptrPointeeOf at h
  cases hk : t.kind with
  | rawPtr m pointee =>
    simp only [hk, Option.map_eq_some_iff] at h
    obtain ⟨⟨s, n⟩, hb, heq⟩ := h
    injection heq with _ hit
    subst hit
    unfold derefPointeeTy translatePointeeRigidTy
    rw [hk]
    cases pointee <;> simp_all [intTyBytes]
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
    | _ => simp [evalOperand, get?, hp, he, hpe, hu]
  | cons _ _ =>
    cases hpe : entry.perm with
    | disabled => exact absurd hpe hperm
    | _ => simp [evalOperand, get?, hp, he, hpe, hu]

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
      ∃ m1, evalPlace m targetPe =
        .ok (({ ptr := { thin_pointer := offsetPtr (localPtr ctx q.local_) relOff, metadata := none },
                 aligned := true }, .Int pointeeIt), m1) ∧
      FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m1 blk stmt) := by
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
        have hbase0 : 0 ≤ ctx.addrs.getD k 0 := haddrOk.2.1
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
        have hloc := ((translateFn_spec body f h.hf).2.1 k d hdk).2
        rw [hTd] at hloc
        have hev := evalPlace_local_some h.shape k (.Int pointeeIt) hloc (localPtr ctx k) hlm_k
        exact ⟨m, by simpa [offsetPtr] using hev, h⟩
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
                have hbase0 : 0 ≤ ctx.addrs.getD k 0 := haddrOk.2.1
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
                obtain ⟨_, m1, hm1, h1⟩ :=
                  (evalPlace_proj h k d hdk pointeeIt count ha (localPtr ctx k) hlm_k
                    (.constantIndex offset minLen fromEnd) hprojOk targetPe hpe).1 idx hprojIdx
                exact ⟨m1, hm1, h1⟩
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
                have hbase0 : 0 ≤ ctx.addrs.getD k 0 := haddrOk.2.1
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
                have hloc := ((translateFn_spec body f h.hf).2.1 k d hdk).2
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
                exact ⟨m, by simpa [TupleSpec.toMiniRustTy] using hpeEval, h⟩
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
      (srcMutbl = .mut → entry.perm = .active) ∧
      entry.targetLocal ∈ bodyAddrTakenLocals body ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) ∧
      evalValue m (.Load (.Local (localName p))) =
        .ok ((.Ptr { thin_pointer := offsetPtr (localPtr ctx entry.targetLocal) relOff, metadata := none },
              thinRawPtrTy), m1) ∧
      FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m1 blk stmt) ∨
    ((view[p]? = some .uninit ∨ view[p]? = some .dead) ∧
      ∃ msg, evalValue m (.Load (.Local (localName p))) = .error (.ub msg)) := by
  have hp_lt : p < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdp).1
  have hisPtr : isPtrTy dp.ty = true := by simp [isPtrTy, hp_ty]
  obtain ⟨hTdp, hitdp⟩ := tyOf_isPtrTy (layouts := body.layouts) hisPtr
  have hloc := ((translateFn_spec body f h.hf).2.1 p dp hdp).2
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
        by simp [evalValue, evalPlace_local_none h.shape p thinRawPtrTy hloc hlm_p]⟩
    | some ptr_p =>
      obtain ⟨id, hpid, _, _, _, _, hAp⟩ := h.locs.storage p dp .dead ptr_p hdp hsp hlm_p
      simp only [hisPtr, ↓reduceIte, declSlotData_of_isPtrTy hisPtr, hitdp] at hAp
      obtain ⟨msg, hmsg⟩ := typedLoad_ptr_thinRawPtr_uninit h.shape ptr_p id hpid hAp
      exact ⟨msg, by simp [evalValue, evalPlace_local_some h.shape p thinRawPtrTy hloc ptr_p hlm_p,
        placeLoad, hmsg]⟩
  | uninit =>
    right
    refine ⟨.inl hsp, ?_⟩
    obtain ⟨ptr_p, hlm_p⟩ := h.locs.some_of_live hsp (by simp)
    obtain ⟨id, hpid, _, _, _, _, hAp⟩ := h.locs.storage p dp .uninit ptr_p hdp hsp hlm_p
    simp only [hisPtr, ↓reduceIte, declSlotData_of_isPtrTy hisPtr, hitdp] at hAp
    obtain ⟨msg, hmsg⟩ := typedLoad_ptr_thinRawPtr_uninit h.shape ptr_p id hpid hAp
    exact ⟨msg, by simp [evalValue, evalPlace_local_some h.shape p thinRawPtrTy hloc ptr_p hlm_p,
      placeLoad, hmsg]⟩
  | init v =>
    left
    obtain ⟨ptrVal, rfl⟩ := (DeclSlotOk_of_isPtrTy hisPtr (.init v)).mp hslotOk
    obtain ⟨entry, relOff, hoff0, hlookup, hmutAct, htspec⟩ :=
      hb.ptr_slots p dp srcMutbl srcIt ptrVal hdp hp_ty hsp
    obtain ⟨hentry_mem, _⟩ := lookupBorrow_mem_and_tag hlookup
    obtain ⟨_, _, _, _, hk_addr, _, _⟩ := hb.entries_ok entry hentry_mem
    obtain ⟨_, _, _, htlt, hptrEq, _, _⟩ :=
      evalTargetPlace h hb hns hfrag ⟨entry.targetLocal, entry.targetProjection⟩ srcIt relOff htspec hk_addr
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
    obtain ⟨m1, hm1, hs1⟩ := typedLoad_ptr_thinRawPtr h.shape ptr_p id hpid _ htlt0 _ hAk
    rw [hptrEq] at hm1
    refine ⟨ptrVal, entry, relOff, m1, hsp, hoff0, hlookup, hmutAct, hk_addr, htspec,
      by simp [evalValue, evalPlace_local_some h.shape p thinRawPtrTy hloc ptr_p hlm_p,
        placeLoad, hm1],
      FrameOk.mk' h.hf hs1 h.locs h.declsOk h.nonScalar⟩

end MiniRustSpec.Correspondence
