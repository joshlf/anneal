/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Lemmas

/-!
# Symbolic evaluation of the MiniRust interpretation on related machines

Each lemma computes one interpreted MiniRust function on a machine whose
thread, active-thread, and allocation fields have the shape fixed by
`StateRel` (`Shape`). The lemmas are stated in terms of the generated MiniRust
types and the interpretation in `MiniRustSpec.Interp`; Anneal does not appear.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

@[simp] theorem pure_ok {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl
@[simp] theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] theorem error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl
@[simp] theorem natCast_lt_zero (n : Nat) : ((n : Int) < 0) ↔ False :=
  iff_of_false (Int.not_lt.mpr (Int.natCast_nonneg n)) id
@[simp] theorem expect_size_sized (s : Size) (a : Align) (msg : String) :
    LayoutStrategy.expect_size (.Sized s a) msg = .ok s := rfl

/-! ## Sizes of fragment integer types -/

/-- The byte sizes of Rust integer types on `x86_64`. -/
def GoodSize (n : Nat) : Prop := n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16

theorem intTyBytes_good {k : MirAst.RigidTy} {s : Signedness} {n : Nat}
    (h : intTyBytes k = some (s, n)) : GoodSize n := by
  unfold intTyBytes at h
  split at h <;> simp at h <;> (obtain ⟨_, rfl⟩ := h) <;> simp [GoodSize]

theorem intTypeOf_good {t : MirAst.Ty} {it : Gen.IntType} (h : intTypeOf t = some it) :
    GoodSize it.size.bytes := by
  unfold intTypeOf at h
  cases hk : intTyBytes t.kind with
  | none => simp [hk] at h
  | some p =>
    obtain ⟨s, n⟩ := p
    simp [hk] at h
    subst h
    exact intTyBytes_good hk

theorem GoodSize.pos {n : Nat} (h : GoodSize n) : 0 < n := by
  rcases h with h | h | h | h | h <;> omega

theorem align_eq (it : Gen.IntType) (h : GoodSize it.size.bytes) :
    IntType.align it = .ok ⟨it.size.bytes⟩ := by
  unfold IntType.align alignFromBytes
  rcases h with h | h | h | h | h <;> rw [h] <;> rfl

theorem layout_eq (it : Gen.IntType) (h : GoodSize it.size.bytes) :
    Type.layout (.Int it) = .ok (.Sized it.size ⟨it.size.bytes⟩) := by
  simp [Type.layout, align_eq it h]

theorem goodAlignBytes_iff (n : Nat) : goodAlignBytes n = true ↔ GoodSize n := by
  simp [goodAlignBytes, GoodSize]

theorem arrayTypeOf_good {t : MirAst.Ty} {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf t = some (elemIt, count)) : GoodSize elemIt.size.bytes := by
  unfold arrayTypeOf at h
  cases hk : t.kind with
  | array elemKind c =>
    simp only [hk] at h
    cases hb : intTyBytes elemKind with
    | none => simp [hb] at h
    | some p =>
      obtain ⟨s, n⟩ := p
      simp [hb] at h
      obtain ⟨rfl, rfl⟩ := h
      exact intTyBytes_good hb
  | _ => simp [hk] at h

theorem translateFn_local_ty {body : CapturedMir} {f : Gen.Function} (hf : translateFn body = some f)
    (i : Nat) (d : LocalDecl) (ty : Gen.Type) (hd : body.localDecls[i]? = some d)
    (hty : translateTy body.layouts d.ty = some ty) :
    mapGet f.locals (localName i) = some ty := by
  obtain ⟨ty', hty', hget⟩ := (translateFn_spec body f hf).2.1 i d hd
  rw [hty] at hty'; cases hty'; exact hget

@[simp] theorem except_bind_ok {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl

@[simp] theorem except_pure {ε α : Type} (x : α) :
    (pure x : Except ε α) = Except.ok x := rfl

@[simp] theorem ensureElseUb_true (msg : String) :
    ensureElseUb true msg = .ok () := rfl

@[simp] theorem ensureElseUb_false (msg : String) :
    ensureElseUb false msg = .error (.ub msg) := rfl

@[simp] theorem int_add_sub_cancel_left (a b : Int) : a + b - a = b := by omega

@[simp] theorem toNat_cast_mul (a b : Nat) : ((a : Int) * (b : Int)).toNat = a * b := by
  have : (a : Int) * (b : Int) = ((a * b : Nat) : Int) := by push_cast; rfl
  rw [this, Int.toNat_natCast]

@[simp] theorem cast_mul_lt_zero (a b : Nat) : ¬ ((a : Int) * (b : Int) < 0) :=
  Int.not_lt.mpr (Int.mul_nonneg (Int.natCast_nonneg a) (Int.natCast_nonneg b))

@[simp] theorem zero_le_cast_mul (a b : Nat) : (0 : Int) ≤ (a : Int) * (b : Int) :=
  Int.mul_nonneg (Int.natCast_nonneg a) (Int.natCast_nonneg b)

@[simp] theorem sizeMulInt_size (s : Size) (m : Nat) :
    Size.mulInt s (Int.ofNat m) = .ok ⟨m * s.bytes⟩ := by
  simp [Size.mulInt, Size.from_bytes, Nat.mul_comm]

@[simp] theorem sizeMulInt_natCast (s : Size) (m : Nat) :
    Size.mulInt s (m : Int) = .ok ⟨m * s.bytes⟩ := by
  simp [Size.mulInt, Size.from_bytes, Nat.mul_comm]

theorem layout_array_eq (elemIt : Gen.IntType) (count : Nat) (h : GoodSize elemIt.size.bytes) :
    Type.layout (.Array (.Int elemIt) (count : Int)) =
      .ok (.Sized ⟨count * elemIt.size.bytes⟩ ⟨elemIt.size.bytes⟩) := by
  unfold Type.layout
  rw [layout_eq elemIt h]
  simp [LayoutStrategy.expect_size, LayoutStrategy.expect_align]

/-! ## The callee's allocations and locals map -/

theorem slotData_length (it : Gen.IntType) (slot : LocalSlot) :
    (slotData it slot).length = it.size.bytes := by
  unfold slotData
  split <;> simp [scalarBytes, uninitBytes, leBytes_length]

theorem declSlotData_length {layouts : Layout.LayoutTable} (d : LocalDecl) (slot : LocalSlot)
    (h : DeclSlotOk layouts d slot) :
    (declSlotData layouts d slot).length =
      match arrayTypeOf d.ty with
      | some (elemIt, count) => count * elemIt.size.bytes
      | none =>
        match tupleTypeOf layouts d.ty with
        | some (_, size, _) => size
        | none => (itOf layouts d).size.bytes := by
  unfold DeclSlotOk at h
  unfold declSlotData
  cases harr : arrayTypeOf d.ty with
  | none =>
    cases htup : tupleTypeOf layouts d.ty with
    | none => exact slotData_length (itOf layouts d) slot
    | some p =>
      obtain ⟨fields, size, align⟩ := p
      simp only [harr, htup] at h ⊢
      cases slot with
      | uninit => simp at h
      | dead => simp at h
      | init val =>
        exact TupleSpec.encodeVal_length (.tuple fields size align) val h.1
  | some p =>
    obtain ⟨elemIt, count⟩ := p
    simp only [harr] at h ⊢
    cases slot with
    | uninit => simp at h
    | dead => simp at h
    | init val =>
      cases val with
      | aggregate vidx elems =>
        cases vidx with
        | zero =>
          simp only at h ⊢
          rw [flatten_map_length (valBytes elemIt) elemIt.size.bytes elems
            (fun x _ => valBytes_length elemIt x), h.1]
        | succ _ => simp at h
      | _ => simp at h

theorem localAllocsFrom_getElem? (layouts : Layout.LayoutTable) (ctx : Ctx) (k : Nat)
    (ds : List LocalDecl) (slots : List LocalSlot)
    (j : Nat) (d : LocalDecl) (slot : LocalSlot) (hd : ds[j]? = some d) (hs : slots[j]? = some slot) :
    (localAllocsFrom layouts ctx k ds slots)[j]? =
      some (localAlloc ctx (k + j) (itOf layouts d) (declSlotData layouts d slot)) := by
  induction ds generalizing k slots j with
  | nil => simp at hd
  | cons d' ds ih =>
    cases slots with
    | nil => simp at hs
    | cons s' ss =>
      cases j with
      | zero => simp at hd hs; subst hd; subst hs; simp [localAllocsFrom]
      | succ j =>
        simp at hd hs
        simp only [localAllocsFrom, List.getElem?_cons_succ]
        rw [ih (k + 1) ss j hd hs, show k + 1 + j = k + (j + 1) by omega]

theorem localAllocsFrom_set (layouts : Layout.LayoutTable) (ctx : Ctx) (k : Nat)
    (ds : List LocalDecl) (slots : List LocalSlot)
    (j : Nat) (d : LocalDecl) (slot' : LocalSlot) (hd : ds[j]? = some d) :
    (localAllocsFrom layouts ctx k ds slots).set j
        (localAlloc ctx (k + j) (itOf layouts d) (declSlotData layouts d slot')) =
      localAllocsFrom layouts ctx k ds (slots.set j slot') := by
  induction ds generalizing k slots j with
  | nil => simp at hd
  | cons d' ds ih =>
    cases slots with
    | nil => simp [localAllocsFrom]
    | cons s' ss =>
      cases j with
      | zero => simp at hd; subst hd; simp [localAllocsFrom]
      | succ j =>
        simp at hd
        simp only [localAllocsFrom, List.set_cons_succ]
        rw [show k + (j + 1) = k + 1 + j by omega, ih (k + 1) ss j hd]

theorem localAllocsFrom_length (layouts : Layout.LayoutTable) (ctx : Ctx) (k : Nat)
    (ds : List LocalDecl) (slots : List LocalSlot) :
    (localAllocsFrom layouts ctx k ds slots).length = min ds.length slots.length := by
  induction ds generalizing k slots with
  | nil => simp [localAllocsFrom]
  | cons d ds ih =>
    cases slots with
    | nil => simp [localAllocsFrom]
    | cons s ss => simp [localAllocsFrom, ih, Nat.min_def]; split <;> omega

theorem mapGet_range_map {V : Type} (g : Nat → V) (n i : Nat) :
    mapGet (⟨(List.range n).map (fun i => (localName i, g i))⟩ : Map Gen.LocalName V) (localName i) =
      if i < n then some (g i) else none := by
  induction n with
  | zero => simp [mapGet]
  | succ n ih =>
    rw [List.range_succ, List.map_append]
    unfold mapGet at ih ⊢
    rw [List.find?_append]
    by_cases hi : i < n
    · have hi' : i < n + 1 := by omega
      simp only [hi, hi', ↓reduceIte] at ih ⊢
      cases h : List.find? (fun e => decide (e.1 = localName i))
        (List.map (fun i => (localName i, g i)) (List.range n)) <;> simp_all
    · cases h : List.find? (fun e => decide (e.1 = localName i))
        (List.map (fun i => (localName i, g i)) (List.range n))
      · by_cases hin : i = n
        · subst hin; simp
        · have : ¬ i < n + 1 := by omega
          simp [localName_inj, Ne.symm hin, this]
      · simp [h, hi] at ih

theorem mapGet_localsMap (ctx : Ctx) (n i : Nat) (hi : i < n) :
    mapGet (localsMap ctx n) (localName i) = some (localPtr ctx i) := by
  simp [localsMap, mapGet_range_map, hi]

/-! ## Machine shape -/

/-- The fields of a MiniRust machine that the fragment's execution reads and
writes: one enabled thread with stack `frames`, active, and the allocation
list. -/
structure Shape (m : Mach) (ctx : Ctx) (frames : List Frame) (allocs : List Gen.Allocation) : Prop where
  threads : m.threads = [thread1 ctx frames]
  active : m.active_thread = 0
  allocs : m.mem.memory.allocations = allocs

theorem curFrame_eq {m : Mach} {ctx : Ctx} {fr : Frame} {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, fr] allocs) : curFrame m = .ok fr := by
  simp [curFrame, activeThread, listIndex, h.threads, h.active, thread1]

theorem pick_eq {m : Mach} {ctx : Ctx} {frs : List Frame} (hthr : m.threads = [thread1 ctx frs]) :
    pickActiveThread m = .ok 0 := by
  simp [pickActiveThread, hthr, thread1]

theorem check_ok (cm : Gen.ConcurrentMemory BM) (S : Set Gen.ThreadId) (acc : List Gen.Access) :
    CM.check_data_races cm 0 (setInsert S 0, acc) = .ok () := by
  unfold CM.check_data_races setContains setInsert
  split <;> simp_all

/-! ## Lists and integer casts -/

@[simp] theorem toNat_cast_add (a b : Nat) : ((a : Int) + (b : Int)).toNat = a + b := by omega

@[simp] theorem cast_add_nonneg (a b : Nat) : (0 : Int) ≤ (a : Int) + (b : Int) := by omega

theorem getElem?_base_append {α : Type} (base L : List α) (i : Nat) :
    (base ++ L)[base.length + i]? = L[i]? := by
  simp [List.getElem?_append_right]

theorem set_base_append {α : Type} (base L : List α) (i : Nat) (x : α) :
    (base ++ L).set (base.length + i) x = base ++ L.set i x := by
  simp

theorem set_self_of_getElem? {α : Type} (L : List α) (i : Nat) (x : α) (h : L[i]? = some x) :
    L.set i x = L := by
  apply List.ext_getElem?
  intro j
  by_cases hij : i = j
  · subst hij; simp [List.getElem?_set_self (List.getElem?_eq_some_iff.mp h).1, h]
  · simp [List.getElem?_set_ne hij]

/-! ## Byte encodings -/

theorem mapM_data_scalarBytes (it : Gen.IntType) (bits : Nat) :
    (scalarBytes it bits).mapM AbstractByte.data = some (leBytes bits it.size.bytes) := by
  unfold scalarBytes
  generalize leBytes bits it.size.bytes = bs
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [List.mapM_cons, AbstractByte.data] at ih ⊢; rw [ih]; rfl

theorem mapM_data_uninitBytes (it : Gen.IntType) (h : 0 < it.size.bytes) :
    (uninitBytes it).mapM AbstractByte.data = none := by
  unfold uninitBytes
  obtain ⟨k, hk⟩ : ∃ k, it.size.bytes = k + 1 := ⟨it.size.bytes - 1, by omega⟩
  rw [hk, List.replicate_succ]
  simp [List.mapM_cons, AbstractByte.data]

theorem decode_leBytes (signed : Signedness) (k bits : Nat) (hb : bits < 2 ^ (8 * k)) :
    Endianness.decode .LittleEndian signed (leBytes bits k) = intFromBits bits ⟨signed, ⟨k⟩⟩ := by
  have hv : leValue (leBytes bits k) = bits := by
    rw [leValue_leBytes, show (256 : Nat) ^ k = 2 ^ (8 * k) by rw [Nat.pow_mul]]
    exact Nat.mod_eq_of_lt hb
  cases signed with
  | Unsigned => simp [Endianness.decode, intFromBits, hv]
  | Signed =>
    simp only [Endianness.decode, intFromBits, hv, leBytes_length]
    by_cases hlt : bits < 2 ^ (8 * k - 1)
    · have : (bits : Int) < 2 ^ (8 * k - 1) := by exact_mod_cast hlt
      simp [hlt, this]
    · have : ¬ (bits : Int) < 2 ^ (8 * k - 1) := by
        intro h'; exact hlt (by exact_mod_cast h')
      simp [hlt, this]

theorem encode_eq (signed : Signedness) (size : Size) (v : Int) (h : inBounds v signed size = true) :
    Endianness.encode .LittleEndian signed size v =
      some (leBytes (v % 2 ^ Size.bits size).toNat size.bytes) := by
  simp [Endianness.encode, h]

theorem canRepresent_intFromBits (it : Gen.IntType) (bits : Nat) (hgood : GoodSize it.size.bytes)
    (hb : bits < 2 ^ (8 * it.size.bytes)) : IntType.can_represent it (intFromBits bits it) = true := by
  have hn : 0 < 8 * it.size.bytes := by have := hgood.pos; omega
  unfold IntType.can_represent
  rw [inBounds_iff _ _ _ (by simpa [Size.bits] using hn)]
  simpa [Size.bits] using intFromBits_window bits it hn hb

/-- Encoding an in-window integer at an integer type yields the little-endian
bytes of its residue. -/
theorem encode_int (it : Gen.IntType) (v : Int) (hgood : GoodSize it.size.bytes)
    (hv : IntType.can_represent it v = true) :
    Type.encode (.Int it) (.Int v) = .ok (scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat) := by
  obtain ⟨signed, size⟩ := it
  have h : inBounds v signed size = true := hv
  simp [Type.encode, x86_64.ENDIANNESS, encode_eq signed size v h, scalarBytes, Size.bits]

/-! ## Loads and stores of the callee's locals -/

@[simp] theorem localAlloc_live (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data : List Byte) :
    (localAlloc ctx i it data).live = true := rfl
@[simp] theorem localAlloc_addr (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data : List Byte) :
    (localAlloc ctx i it data).addr = ctx.addrs.getD i 0 := rfl
@[simp] theorem localAlloc_data (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data : List Byte) :
    (localAlloc ctx i it data).data = data := rfl
@[simp] theorem localAlloc_align (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data : List Byte) :
    (localAlloc ctx i it data).align = ⟨it.size.bytes⟩ := rfl
@[simp] theorem localAlloc_kind (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data : List Byte) :
    (localAlloc ctx i it data).kind = .Stack := rfl

/-- The machine after loading or storing: the access is logged, the
allocations are `allocs`, and nothing else changes. -/
def withMem (m : Mach) (allocs : List Gen.Allocation) (acc : Gen.Access) : Mach :=
  { m with mem := { memory := { m.mem.memory with allocations := allocs },
                    accesses := m.mem.accesses ++ [acc] } }

theorem withMem_shape {m : Mach} {ctx : Ctx} {frames : List Frame} {allocs allocs' : List Gen.Allocation}
    (h : Shape m ctx frames allocs) (acc : Gen.Access) :
    Shape (withMem m allocs' acc) ctx frames allocs' :=
  ⟨h.threads, h.active, rfl⟩

/-- `Align::ONE`, and the natural alignment of a local, accept its address. -/
@[simp] theorem isAligned_one (a : Int) : Align.is_aligned ⟨1⟩ a = true := by
  simp [Align.is_aligned]

theorem typedLoad_local_init {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType) (bits : Nat)
    (hgood : GoodSize it.size.bytes) (hb : bits < 2 ^ (8 * it.size.bytes))
    (hL : L[i]? = some (localAlloc ctx i it (scalarBytes it bits)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) (.Int it) align .None = .ok (.Int (intFromBits bits it), m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hlen : (scalarBytes it bits).length = it.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD i 0, it.size⟩, ?_,
    withMem_shape h _⟩
  obtain ⟨signed, size⟩ := it
  simp only [typedLoad, layout_eq _ hgood, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [Nat.ne_of_gt hpos, hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset,
    List.take_of_length_le, Type.decode, mapM_data_scalarBytes, x86_64.ENDIANNESS,
    decode_leBytes signed size.bytes bits hb, checkValue, canRepresent_intFromBits _ bits hgood hb,
    withMem]

theorem typedLoad_local_uninit {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes) (hL : L[i]? = some (localAlloc ctx i it (uninitBytes it)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) (.Int it) align .None = .error (.ub msg) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hlen : (uninitBytes it).length = it.size.bytes := by simp [uninitBytes]
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨"load at type but the data in memory violates the language invariant", ?_⟩
  obtain ⟨signed, size⟩ := it
  simp only [typedLoad, layout_eq _ hgood, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [Nat.ne_of_gt hpos, hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset,
    List.take_of_length_le, Type.decode, mapM_data_uninitBytes _ hpos, ub]

theorem localAlloc_with_data (ctx : Ctx) (i : Nat) (it : Gen.IntType) (data data' : List Byte) :
    { localAlloc ctx i it data with data := data' } = localAlloc ctx i it data' := rfl

theorem typedStore_local {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType) (data : List Byte) (v : Int)
    (hgood : GoodSize it.size.bytes) (hL : L[i]? = some (localAlloc ctx i it data))
    (hlen : data.length = it.size.bytes) (hv : IntType.can_represent it v = true)
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    typedStore m (localPtr ctx i) (.Int v) (.Int it) align .None =
      .ok (withMem m (ctx.base ++ L.set i
              (localAlloc ctx i it (scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat)))
            ⟨.Store, .None, ctx.addrs.getD i 0, it.size⟩) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hblen : (scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat).length = it.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hck : checkValue (.Int v) (.Int it) = .ok () := by simp [checkValue, hv]
  have hne : scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  simp only [typedStore, hck, encode_int it v hgood hv, CM.store, BM.store, hal, BM.check_ptr,
    localPtr, listIndex, h.allocs]
  obtain ⟨signed, size⟩ := it
  have hdrop : data.drop size.bytes = [] := List.drop_eq_nil_of_le (by simp at hlen; omega)
  simp [hne, hi, hLi, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem, hdrop]
  simp [localAlloc]

/-! ## Array encodings, loads, stores, and indexed places -/

/-- MiniRust `Val` corresponding to an Anneal scalar `Value` at element type
`elemIt`. -/
def valToMiniRust (elemIt : Gen.IntType) : Value → Val
  | .scalar sc => .Int (intFromBits sc.bits elemIt)
  | _ => .Int 0

/-- Pointer to element `idx` of array local `_j` (`localPtr ctx j` offset by
`idx * elemIt.size.bytes`). -/
def elemPtr (ctx : Ctx) (j idx : Nat) (elemIt : Gen.IntType) : Ptr :=
  { (localPtr ctx j) with addr := ctx.addrs.getD j 0 + ((idx * elemIt.size.bytes : Nat) : Int) }

theorem decode_valBytes (elemIt : Gen.IntType) (v : Value) (hv : ElemOk elemIt v) :
    Type.decode (.Int elemIt) (valBytes elemIt v) = .ok (some (valToMiniRust elemIt v)) := by
  cases v <;> simp [ElemOk] at hv
  rename_i sc
  obtain ⟨_, hb⟩ := hv
  rcases elemIt with ⟨signed, ⟨k⟩⟩
  have hlen : (scalarBytes ⟨signed, ⟨k⟩⟩ sc.bits).length = k := by
    simp [scalarBytes, leBytes_length]
  simp [valBytes, valToMiniRust, Type.decode, hlen, mapM_data_scalarBytes, x86_64.ENDIANNESS,
    decode_leBytes signed k sc.bits hb]

theorem checkValue_valToMiniRust (elemIt : Gen.IntType) (hgood : GoodSize elemIt.size.bytes)
    (v : Value) (hv : ElemOk elemIt v) :
    checkValue (valToMiniRust elemIt v) (.Int elemIt) = .ok () := by
  cases v <;> simp [ElemOk] at hv
  rename_i sc
  obtain ⟨_, hb⟩ := hv
  simp [valToMiniRust, checkValue, canRepresent_intFromBits elemIt sc.bits hgood hb]

theorem encode_valToMiniRust (elemIt : Gen.IntType) (hgood : GoodSize elemIt.size.bytes)
    (v : Value) (hv : ElemOk elemIt v) :
    Type.encode (.Int elemIt) (valToMiniRust elemIt v) = .ok (valBytes elemIt v) := by
  cases v <;> simp [ElemOk] at hv
  rename_i sc
  obtain ⟨_, hb⟩ := hv
  have hrep := canRepresent_intFromBits elemIt sc.bits hgood hb
  simp [valToMiniRust, valBytes, encode_int elemIt _ hgood hrep, intFromBits_emod sc.bits elemIt hb]

theorem mapM_except_append {ε α β : Type} (f : α → Except ε β) (xs ys : List α)
    (us vs : List β) (hx : xs.mapM f = .ok us) (hy : ys.mapM f = .ok vs) :
    (xs ++ ys).mapM f = .ok (us ++ vs) := by
  induction xs generalizing us with
  | nil => simp [List.mapM_nil] at hx; subst hx; simpa using hy
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, Except.bind] at hx
    cases hfx : f x with
    | error e => simp [hfx] at hx
    | ok u =>
      cases hxs : xs.mapM f with
      | error e => simp [hfx, hxs] at hx
      | ok us' =>
        simp [hfx, hxs] at hx; subst hx
        simp [List.cons_append, List.mapM_cons, bind, Except.bind, hfx, ih us' hxs]

theorem mapM_range_prefix {ε α β : Type} (xs : List α) (f : α → β) (g : Nat → Except ε β)
    (n : Nat) (hn : n ≤ xs.length)
    (hg : ∀ (i : Nat) (hi : i < n), g i = .ok (f (xs[i]'(Nat.lt_of_lt_of_le hi hn)))) :
    (List.range n).mapM g = .ok ((xs.take n).map f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ]
    have ih' := ih (by omega) (fun i hi => hg i (by omega))
    have hlast : [n].mapM g = .ok [f (xs[n]'(by omega))] := by
      simp [List.mapM_cons, List.mapM_nil, hg n (by omega)]
    rw [mapM_except_append g (List.range n) [n] _ _ ih' hlast]
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      List.map_append, List.map_singleton]

theorem mapM_decode_valBytes (elemIt : Gen.IntType) (elems : List Value)
    (he : ∀ v ∈ elems, ElemOk elemIt v) :
    tryMapM (fun elemBytes => Type.decode (.Int elemIt) elemBytes)
        (elems.map (valBytes elemIt)) =
      .ok (some (elems.map (valToMiniRust elemIt))) := by
  induction elems with
  | nil => rfl
  | cons v vs ih =>
    have hv := decode_valBytes elemIt v (he v (by simp))
    have ih' := ih (fun x hx => he x (by simp [hx]))
    simp [tryMapM, hv, ih']

theorem decode_array (elemIt : Gen.IntType) (hgood : GoodSize elemIt.size.bytes)
    (elems : List Value) (count : Nat) (hlen : elems.length = count)
    (he : ∀ v ∈ elems, ElemOk elemIt v) :
    Type.decode (.Array (.Int elemIt) (count : Int))
        ((elems.map (valBytes elemIt)).flatten) =
      .ok (some (.Tuple (elems.map (valToMiniRust elemIt)))) := by
  have hblen : ((elems.map (valBytes elemIt)).flatten).length = count * elemIt.size.bytes := by
    rw [flatten_map_length (valBytes elemIt) elemIt.size.bytes elems
      (fun x _ => valBytes_length elemIt x), hlen]
  have hchunks : (List.range count).mapM (fun (i : Nat) =>
      subsliceWithLength ((elems.map (valBytes elemIt)).flatten)
        ((i : Int) * (elemIt.size.bytes : Int)) elemIt.size.bytes) =
      .ok (elems.map (valBytes elemIt)) := by
    subst hlen
    have hpref := mapM_range_prefix elems (valBytes elemIt)
      (fun (i : Nat) =>
        subsliceWithLength ((elems.map (valBytes elemIt)).flatten)
          ((i : Int) * (elemIt.size.bytes : Int)) elemIt.size.bytes)
      elems.length (Nat.le_refl _)
      (fun i hi => by
        rw [← Int.natCast_mul]
        exact subsliceWithLength_flatten_map (valBytes elemIt) elemIt.size.bytes elems
          (fun x _ => valBytes_length elemIt x) i elems[i] (List.getElem?_eq_getElem hi))
    simpa [List.take_length] using hpref
  have hdec := mapM_decode_valBytes elemIt elems he
  unfold Type.decode
  rw [layout_eq elemIt hgood]
  simp only [LayoutStrategy.expect_size, except_bind_ok, except_pure, sizeMulInt_natCast,
    Int.toNat_natCast, hblen, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hchunks]
  simp only [except_bind_ok]
  change (do
    let decoded ← tryMapM (fun elemBytes => Type.decode (.Int elemIt) elemBytes)
      (elems.map (valBytes elemIt))
    pure (decoded.map Gen.Value.Tuple)) = _
  rw [hdec]
  rfl

theorem checkValue_forM_valToMiniRust (elemIt : Gen.IntType) (hgood : GoodSize elemIt.size.bytes)
    (elems : List Value) (he : ∀ v ∈ elems, ElemOk elemIt v) :
    (elems.map (valToMiniRust elemIt)).forM (fun v => checkValue v (.Int elemIt)) = .ok () := by
  induction elems with
  | nil => rfl
  | cons v vs ih =>
    have hv := checkValue_valToMiniRust elemIt hgood v (he v (by simp))
    have ih' := ih (fun x hx => he x (by simp [hx]))
    rw [List.map_cons]
    change (do checkValue (valToMiniRust elemIt v) (.Int elemIt); (vs.map (valToMiniRust elemIt)).forM (fun v => checkValue v (.Int elemIt))) = .ok ()
    rw [hv, except_bind_ok, ih']

theorem checkValue_array (elemIt : Gen.IntType) (hgood : GoodSize elemIt.size.bytes)
    (elems : List Value) (count : Nat) (hlen : elems.length = count)
    (he : ∀ v ∈ elems, ElemOk elemIt v) :
    checkValue (.Tuple (elems.map (valToMiniRust elemIt)))
        (.Array (.Int elemIt) (count : Int)) = .ok () := by
  have hm := checkValue_forM_valToMiniRust elemIt hgood elems he
  unfold checkValue
  simp [hlen, hm]

theorem encode_map_valToMiniRust (elemIt : Gen.IntType) (hgood : GoodSize elemIt.size.bytes)
    (elems : List Value) (he : ∀ v ∈ elems, ElemOk elemIt v) :
    (elems.map (valToMiniRust elemIt)).mapM (fun value => do
      let bytes ← Type.encode (.Int elemIt) value
      let elemLayout ← Type.layout (.Int elemIt)
      let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array element is sized"
      if bytes.length ≠ elemSize.bytes then
        specPanic "encode: Type::Array element byte length mismatch"
      else
        pure bytes) = .ok (elems.map (valBytes elemIt)) := by
  induction elems with
  | nil => rfl
  | cons v vs ih =>
    have hv := encode_valToMiniRust elemIt hgood v (he v (by simp))
    have hlen := valBytes_length elemIt v
    have ih' := ih (fun x hx => he x (by simp [hx]))
    rw [List.map_cons, List.mapM_cons, hv, ih', layout_eq elemIt hgood]
    simp [hlen]

theorem encode_array (elemIt : Gen.IntType) (hgood : GoodSize elemIt.size.bytes)
    (elems : List Value) (count : Nat) (hlen : elems.length = count)
    (he : ∀ v ∈ elems, ElemOk elemIt v) :
    Type.encode (.Array (.Int elemIt) (count : Int))
        (.Tuple (elems.map (valToMiniRust elemIt))) =
      .ok ((elems.map (valBytes elemIt)).flatten) := by
  have hm := encode_map_valToMiniRust elemIt hgood elems he
  unfold Type.encode
  simp only [List.length_map, hlen, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hm]
  rfl

theorem memory_with_allocs_self (mem : BM) (allocs : List Gen.Allocation)
    (h : mem.allocations = allocs) :
    { mem with allocations := allocs } = mem := by
  cases mem; subst h; rfl

theorem typedLoad_array_local {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (j : Nat) (elemIt : Gen.IntType) (count : Nat)
    (elems : List Value) (hgood : GoodSize elemIt.size.bytes) (hlen : elems.length = count)
    (he : ∀ v ∈ elems, ElemOk elemIt v)
    (hL : L[j]? = some (localAlloc ctx j elemIt ((elems.map (valBytes elemIt)).flatten))) :
    ∃ m', typedLoad m (localPtr ctx j) (.Array (.Int elemIt) (count : Int)) ⟨1⟩ .None =
        .ok (.Tuple (elems.map (valToMiniRust elemIt)), m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  obtain ⟨hj, hLj⟩ := List.getElem?_eq_some_iff.mp hL
  have hblen : ((elems.map (valBytes elemIt)).flatten).length = count * elemIt.size.bytes := by
    rw [flatten_map_length (valBytes elemIt) elemIt.size.bytes elems (fun x _ => valBytes_length elemIt x), hlen]
  have hset := set_self_of_getElem? L j _ hL
  have hdec := decode_array elemIt hgood elems count hlen he
  have hck := checkValue_array elemIt hgood elems count hlen he
  have hload : CM.load m.mem (localPtr ctx j) ⟨count * elemIt.size.bytes⟩ ⟨1⟩ .None =
      .ok ((elems.map (valBytes elemIt)).flatten,
        (withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD j 0, ⟨count * elemIt.size.bytes⟩⟩).mem) := by
    by_cases hc : count * elemIt.size.bytes = 0
    · have hc0 : count = 0 := by
        rcases Nat.eq_zero_or_pos count with rfl | hpos
        · rfl
        · exfalso; exact Nat.ne_of_gt (Nat.mul_pos hpos hgood.pos) hc
      subst hc0
      have hel0 : elems = [] := List.eq_nil_of_length_eq_zero hlen
      subst hel0
      simp [CM.load, BM.load, BM.check_ptr, localPtr, withMem,
        memory_with_allocs_self m.mem.memory _ h.allocs]
    · simp only [CM.load, BM.load, isAligned_one, BM.check_ptr, localPtr, listIndex, h.allocs]
      simp [hc, hj, hLj, Allocation.size, hblen, listSet, subsliceWithLength, hset,
        List.take_of_length_le, withMem]
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD j 0, ⟨count * elemIt.size.bytes⟩⟩,
    ?_, withMem_shape h _⟩
  unfold typedLoad
  rw [layout_array_eq elemIt count hgood]
  simp only [expect_size_sized, except_bind_ok]
  rw [hload]
  simp only [except_bind_ok]
  rw [hdec]
  simp only [except_bind_ok, hck, except_pure]
  rfl

theorem typedStore_array_local {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (elemIt : Gen.IntType) (count : Nat)
    (data : List Byte) (elems : List Value) (hgood : GoodSize elemIt.size.bytes)
    (hL : L[i]? = some (localAlloc ctx i elemIt data))
    (hdlen : data.length = count * elemIt.size.bytes)
    (hlen : elems.length = count) (he : ∀ v ∈ elems, ElemOk elemIt v) :
    typedStore m (localPtr ctx i) (.Tuple (elems.map (valToMiniRust elemIt)))
        (.Array (.Int elemIt) (count : Int)) ⟨1⟩ .None =
      .ok (withMem m (ctx.base ++ L.set i
              (localAlloc ctx i elemIt ((elems.map (valBytes elemIt)).flatten)))
            ⟨.Store, .None, ctx.addrs.getD i 0, ⟨count * elemIt.size.bytes⟩⟩) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hblen : ((elems.map (valBytes elemIt)).flatten).length = count * elemIt.size.bytes := by
    rw [flatten_map_length (valBytes elemIt) elemIt.size.bytes elems (fun x _ => valBytes_length elemIt x), hlen]
  have hck := checkValue_array elemIt hgood elems count hlen he
  have henc := encode_array elemIt hgood elems count hlen he
  have hstore : CM.store m.mem (localPtr ctx i) ((elems.map (valBytes elemIt)).flatten) ⟨1⟩ .None =
      .ok (withMem m (ctx.base ++ L.set i
              (localAlloc ctx i elemIt ((elems.map (valBytes elemIt)).flatten)))
            ⟨.Store, .None, ctx.addrs.getD i 0, ⟨count * elemIt.size.bytes⟩⟩).mem := by
    by_cases hc : count * elemIt.size.bytes = 0
    · have hc0 : count = 0 := by
        rcases Nat.eq_zero_or_pos count with rfl | hpos
        · rfl
        · exfalso; exact Nat.ne_of_gt (Nat.mul_pos hpos hgood.pos) hc
      subst hc0
      have hel0 : elems = [] := List.eq_nil_of_length_eq_zero hlen
      subst hel0
      have hdnil : data = [] := List.eq_nil_of_length_eq_zero (by simpa using hdlen)
      subst hdnil
      have hset := set_self_of_getElem? L i _ hL
      simp [CM.store, BM.store, BM.check_ptr, localPtr, withMem, hset,
        memory_with_allocs_self m.mem.memory _ h.allocs]
    · have hdrop : data.drop (count * elemIt.size.bytes) = [] :=
        List.drop_eq_nil_of_le (by omega)
      simp only [CM.store, BM.store, isAligned_one, BM.check_ptr, hblen, hc, ↓reduceIte,
        localPtr, listIndex, h.allocs]
      simp [hi, hLi, Allocation.size, hdlen, hblen, writeSubsliceAtIndex, listSet,
        withMem, hdrop]
      simp [localAlloc]
  unfold typedStore
  rw [hck]
  simp only
  rw [henc, except_bind_ok, hstore]
  rfl

theorem typedLoad_array_elem {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (j idx : Nat) (elemIt : Gen.IntType) (count : Nat)
    (elems : List Value) (sc : ScalarVal) (hgood : GoodSize elemIt.size.bytes)
    (hlen : elems.length = count) (he : ∀ v ∈ elems, ElemOk elemIt v)
    (hsc : elems[idx]? = some (.scalar sc))
    (hL : L[j]? = some (localAlloc ctx j elemIt ((elems.map (valBytes elemIt)).flatten))) :
    ∃ m', typedLoad m (elemPtr ctx j idx elemIt) (.Int elemIt) ⟨1⟩ .None =
        .ok (.Int (intFromBits sc.bits elemIt), m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  obtain ⟨signed, ⟨bytes⟩⟩ := elemIt
  have hpos := hgood.pos
  obtain ⟨hj, hLj⟩ := List.getElem?_eq_some_iff.mp hL
  have hidx : idx < elems.length := (List.getElem?_eq_some_iff.mp hsc).1
  obtain ⟨hsz, hb⟩ := he (.scalar sc) (List.mem_of_getElem? hsc)
  have hblen : ((elems.map (valBytes ⟨signed, ⟨bytes⟩⟩)).flatten).length = count * bytes := by
    rw [flatten_map_length (valBytes ⟨signed, ⟨bytes⟩⟩) bytes elems (fun x _ => valBytes_length ⟨signed, ⟨bytes⟩⟩ x), hlen]
  have hscLen : (scalarBytes ⟨signed, ⟨bytes⟩⟩ sc.bits).length = bytes := by
    simp [scalarBytes, leBytes_length]
  have hsub := subsliceWithLength_flatten_map (valBytes ⟨signed, ⟨bytes⟩⟩) bytes elems
    (fun x _ => valBytes_length ⟨signed, ⟨bytes⟩⟩ x) idx (.scalar sc) hsc
  simp only [valBytes, Int.natCast_mul] at hsub
  have hset := set_self_of_getElem? L j _ hL
  have hoff_le : idx * bytes + bytes ≤ count * bytes :=
    calc idx * bytes + bytes
      _ = (idx + 1) * bytes := (Nat.succ_mul idx bytes).symm
      _ ≤ count * bytes := Nat.mul_le_mul_right _ (by omega)
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, (elemPtr ctx j idx ⟨signed, ⟨bytes⟩⟩).addr, ⟨bytes⟩⟩,
    ?_, withMem_shape h _⟩
  have hchk2 : ¬ ((count : Int) * (bytes : Int) <
      (idx : Int) * (bytes : Int) + (bytes : Int)) := by
    exact_mod_cast Nat.not_lt.mpr hoff_le
  simp only [typedLoad, layout_eq _ hgood, CM.load, BM.load,
    BM.check_ptr, elemPtr, localPtr, listIndex, h.allocs]
  simp [Nat.ne_of_gt hpos, hj, hLj, Allocation.size, hblen, hchk2, listSet, hsub, hset,
    Type.decode, hscLen, mapM_data_scalarBytes, x86_64.ENDIANNESS,
    decode_leBytes signed bytes sc.bits hb,
    checkValue, canRepresent_intFromBits _ sc.bits hgood hb, withMem]

theorem typedStore_array_elem {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i idx : Nat) (elemIt : Gen.IntType) (count : Nat)
    (elems : List Value) (r : Nat) (hgood : GoodSize elemIt.size.bytes)
    (hlen : elems.length = count) (hidx : idx < count) (hr : r < 2 ^ (8 * elemIt.size.bytes))
    (hL : L[i]? = some (localAlloc ctx i elemIt ((elems.map (valBytes elemIt)).flatten))) :
    typedStore m (elemPtr ctx i idx elemIt) (.Int (intFromBits r elemIt)) (.Int elemIt) ⟨1⟩ .None =
      .ok (withMem m (ctx.base ++ L.set i
              (localAlloc ctx i elemIt
                (((elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩)).map (valBytes elemIt)).flatten)))
            ⟨.Store, .None, (elemPtr ctx i idx elemIt).addr, elemIt.size⟩) := by
  obtain ⟨signed, ⟨bytes⟩⟩ := elemIt
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hrep := canRepresent_intFromBits ⟨signed, ⟨bytes⟩⟩ r hgood hr
  have hck : checkValue (.Int (intFromBits r ⟨signed, ⟨bytes⟩⟩)) (.Int ⟨signed, ⟨bytes⟩⟩) = .ok () := by
    simp [checkValue, hrep]
  have hblen : ((elems.map (valBytes ⟨signed, ⟨bytes⟩⟩)).flatten).length = count * bytes := by
    rw [flatten_map_length (valBytes ⟨signed, ⟨bytes⟩⟩) bytes elems (fun x _ => valBytes_length ⟨signed, ⟨bytes⟩⟩ x), hlen]
  have hscLen : (scalarBytes ⟨signed, ⟨bytes⟩⟩ r).length = bytes := by
    simp [scalarBytes, leBytes_length]
  have hres : (intFromBits r ⟨signed, ⟨bytes⟩⟩ % 2 ^ (8 * bytes)).toNat = r := by
    rw [intFromBits_emod r _ hr]; simp
  have hoff_le : idx * bytes + bytes ≤ count * bytes :=
    calc idx * bytes + bytes
      _ = (idx + 1) * bytes := (Nat.succ_mul idx bytes).symm
      _ ≤ count * bytes := Nat.mul_le_mul_right _ (by omega)
  have hsplice := splice_flatten_map (valBytes ⟨signed, ⟨bytes⟩⟩) bytes elems
    (fun x _ => valBytes_length ⟨signed, ⟨bytes⟩⟩ x) idx (.scalar ⟨r, bytes⟩) (by omega)
  simp only [valBytes] at hsplice
  have hchk2 : ¬ ((count : Int) * (bytes : Int) <
      (idx : Int) * (bytes : Int) + (bytes : Int)) := by
    exact_mod_cast Nat.not_lt.mpr hoff_le
  have hchk3 : (idx : Int) * (bytes : Int) + (bytes : Int) ≤
      (count : Int) * (bytes : Int) := by
    exact_mod_cast hoff_le
  simp only [typedStore, hck, encode_int ⟨signed, ⟨bytes⟩⟩ _ hgood hrep, hres, except_bind_ok,
    CM.store, BM.store, BM.check_ptr, hscLen, Nat.ne_of_gt hpos, ↓reduceIte,
    elemPtr, localPtr, listIndex, h.allocs]
  simp [hi, hLi, Allocation.size, hblen, hscLen, hchk2, hchk3,
    writeSubsliceAtIndex, listSet, withMem, localAlloc]
  rw [← List.append_assoc, hsplice, List.map_set, valBytes]

theorem ptrOffsetInbounds_local {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (j : Nat) (it : Gen.IntType) (data : List Byte)
    (hL : L[j]? = some (localAlloc ctx j it data)) (off : Nat) (hoff : off ≤ data.length)
    (hbound : off < 2 ^ 63) (haddr0 : 0 ≤ ctx.addrs.getD j 0)
    (haddrMax : ctx.addrs.getD j 0 + (data.length : Int) < 2 ^ 64) :
    ptrOffsetInbounds m (localPtr ctx j) (off : Int) =
      .ok { (localPtr ctx j) with addr := ctx.addrs.getD j 0 + (off : Int) } := by
  obtain ⟨hj, hLj⟩ := List.getElem?_eq_some_iff.mp hL
  have hderef : CM.signed_dereferenceable m.mem (localPtr ctx j) (off : Int) = .ok () := by
    unfold CM.signed_dereferenceable BM.signed_dereferenceable Size.from_bytes
      BM.dereferenceable BM.check_ptr
    have h0 : 0 ≤ (off : Int) := by omega
    simp only [h0, ↓reduceIte, Int.toNat_natCast]
    by_cases hoff0 : off = 0
    · simp [hoff0]
    · have hle : ¬ ((off : Int) > (data.length : Int)) := by omega
      simp [hoff0, localPtr, listIndex, h.allocs, hj, hLj, Allocation.size, hle]
  have hb1 : inBounds (off : Int) .Signed x86_64.PTR_SIZE = true := by
    rw [inBounds_iff _ _ _ (by decide)]
    simp only [windowLo, x86_64.PTR_SIZE, Size.bits]
    omega
  have hb2 : inBounds ((localPtr ctx j).addr + (off : Int)) .Unsigned x86_64.PTR_SIZE = true := by
    rw [inBounds_iff _ _ _ (by decide)]
    simp only [windowLo, x86_64.PTR_SIZE, Size.bits, localPtr]
    omega
  unfold ptrOffsetInbounds
  rw [hderef, except_bind_ok, hb1, hb2]
  simp [localPtr]

theorem ptrOffsetInbounds_elem {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (j idx : Nat) (elemIt : Gen.IntType) (data : List Byte)
    (hL : L[j]? = some (localAlloc ctx j elemIt data))
    (hoff : idx * elemIt.size.bytes ≤ data.length)
    (hbound : idx * elemIt.size.bytes < 2 ^ 63) (haddr0 : 0 ≤ ctx.addrs.getD j 0)
    (haddrMax : ctx.addrs.getD j 0 + (data.length : Int) < 2 ^ 64) :
    ptrOffsetInbounds m (localPtr ctx j) ((idx : Int) * (elemIt.size.bytes : Int)) =
      .ok (elemPtr ctx j idx elemIt) := by
  have hptr := ptrOffsetInbounds_local h j elemIt data hL (idx * elemIt.size.bytes) hoff hbound haddr0 haddrMax
  simpa [Int.natCast_mul, elemPtr, localPtr] using hptr

/-! ## Places of the callee's locals -/

theorem evalPlace_local {m : Mach} {ctx : Ctx} {f : Gen.Function} {n blk stmt : Nat}
    {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrame f ctx n blk stmt] allocs) (i : Nat) (hi : i < n)
    (T : Gen.Type) (hT : mapGet f.locals (localName i) = some T) :
    evalPlace m (.Local (localName i)) =
      .ok (({ ptr := { thin_pointer := localPtr ctx i, metadata := none }, aligned := true }, T), m) := by
  simp [evalPlace, curFrame_eq h, mapIndex, calleeFrame, hT, mapGet_localsMap ctx n i hi]

/-! ## Tuple and struct encodings, loads, stores, and field places -/

theorem head_size_and_align_mk (size align : Nat) (hmod : size % align = 0) :
    TupleHeadLayout.head_size_and_align
      { «end» := ⟨size⟩, align := ⟨align⟩, packed_align := none } =
      (⟨size⟩, ⟨align⟩) := by
  simp [TupleHeadLayout.head_size_and_align, Size.align_to, hmod]

theorem layout_tupleSpec (s : TupleSpec) (hwf : s.wf = true) :
    Type.layout s.toMiniRustTy = .ok (.Sized ⟨s.size⟩ ⟨s.align⟩) := by
  cases s with
  | scalar it =>
    simp only [TupleSpec.wf] at hwf
    exact layout_eq it ((goodAlignBytes_iff it.size.bytes).mp hwf)
  | tuple fields size align =>
    simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨⟨_, hmod⟩, _⟩, _⟩ := hwf
    simp [TupleSpec.toMiniRustTy, Type.layout, head_size_and_align_mk size align hmod,
      TupleSpec.size, TupleSpec.align]

mutual

theorem decode_tupleSpec (s : TupleSpec) (v : Value)
    (hwf : s.wf = true) (hv : s.valOk v = true) :
    Type.decode s.toMiniRustTy (s.encodeVal v) = .ok (some (s.toMiniRustVal v)) := by
  cases s with
  | scalar it =>
    cases v with
    | scalar sc =>
      simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨hsz, hb⟩ := hv
      have hd := decode_valBytes it (.scalar sc) ⟨hsz, hb⟩
      simpa [TupleSpec.toMiniRustTy, TupleSpec.encodeVal, TupleSpec.toMiniRustVal,
        valBytes, valToMiniRust] using hd
    | _ => simp [TupleSpec.valOk] at hv
  | tuple fields size align =>
    cases v with
    | aggregate vidx vals =>
      cases vidx with
      | succ _ => simp [TupleSpec.valOk] at hv
      | zero =>
        have hblen := TupleSpec.encodeVal_length (.tuple fields size align) (.aggregate 0 vals) hwf
        simp only [TupleSpec.encodeVal, TupleSpec.size] at hblen
        simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hv
        obtain ⟨_, hfwv⟩ := hv
        simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
        obtain ⟨⟨⟨_, hmod⟩, _⟩, hfwf⟩ := hwf
        have hfields := decodeTupleFields_spec size align fields vals
          (List.replicate size Gen.AbstractByte.Uninit) hfwf hfwv (by simp)
        unfold TupleSpec.toMiniRustTy TupleSpec.encodeVal TupleSpec.toMiniRustVal Type.decode
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          head_size_and_align_mk size align hmod, hblen, ne_eq, not_true_eq_false]
        rw [hfields]
        rfl
    | _ => simp [TupleSpec.valOk] at hv

theorem decodeTupleFields_spec (size align : Nat) (fields : List (Nat × TupleSpec))
    (vals : List Value) (acc : List Byte)
    (hfwf : TupleSpec.fieldsWf size align fields = true)
    (hv : TupleSpec.fieldsValOk fields vals = true)
    (hacc : acc.length = size) :
    decodeTupleFields (TupleSpec.fieldsToMiniRust fields)
        (TupleSpec.encodeFields fields vals acc) =
      .ok (some (TupleSpec.fieldsToMiniRustVal fields vals)) := by
  cases fields with
  | nil =>
    cases vals <;> simp [TupleSpec.fieldsValOk] at hv
    simp [TupleSpec.fieldsToMiniRust, TupleSpec.fieldsToMiniRustVal, decodeTupleFields]
  | cons f restF =>
    obtain ⟨off, fs⟩ := f
    cases vals with
    | nil => simp [TupleSpec.fieldsValOk] at hv
    | cons v restV =>
      have hlen_enc : (TupleSpec.encodeFields ((off, fs) :: restF) (v :: restV) acc).length = size :=
        TupleSpec.encodeFields_length size align ((off, fs) :: restF) (v :: restV) acc hfwf hacc
      obtain ⟨hfswf, hoff, _, _, hslice⟩ :=
        TupleSpec.encodeFields_field_slice size align ((off, fs) :: restF) (v :: restV) acc
          0 off fs v hfwf hacc rfl rfl
      simp only [TupleSpec.fieldsWf, Bool.and_eq_true] at hfwf
      have hrestWf := hfwf.2
      simp only [TupleSpec.fieldsValOk, Bool.and_eq_true] at hv
      obtain ⟨hvv, hrestV⟩ := hv
      have hlay := layout_tupleSpec fs hfswf
      have hsub : subsliceWithLength (TupleSpec.encodeFields ((off, fs) :: restF) (v :: restV) acc)
          (off : Int) (fs.size : Int) = .ok (fs.encodeVal v) := by
        rw [subsliceWithLength_eq_drop_take _ off fs.size (by omega), hslice]
      have hdec_head := decode_tupleSpec fs v hfswf hvv
      have hlen_v := TupleSpec.encodeVal_length fs v hfswf
      have hacc' : (spliceAt acc off (fs.encodeVal v)).length = size := by
        rw [spliceAt_length _ _ _ (by omega), hacc]
      have hdec_tail := decodeTupleFields_spec size align restF restV
        (spliceAt acc off (fs.encodeVal v)) hrestWf hrestV hacc'
      unfold TupleSpec.fieldsToMiniRust TupleSpec.fieldsToMiniRustVal decodeTupleFields
      rw [hlay]
      simp only [expect_size_sized, except_bind_ok]
      rw [hsub, except_bind_ok, hdec_head, except_bind_ok]
      change (do
        match ← decodeTupleFields (TupleSpec.fieldsToMiniRust restF)
            (TupleSpec.encodeFields restF restV (spliceAt acc off (fs.encodeVal v))) with
        | none => pure none
        | some vs => pure (some (fs.toMiniRustVal v :: vs))) = _
      rw [hdec_tail]
      rfl

end

mutual

theorem checkValue_tupleSpec (s : TupleSpec) (v : Value)
    (hwf : s.wf = true) (hv : s.valOk v = true) :
    checkValue (s.toMiniRustVal v) s.toMiniRustTy = .ok () := by
  cases s with
  | scalar it =>
    simp only [TupleSpec.wf] at hwf
    have hgood := (goodAlignBytes_iff it.size.bytes).mp hwf
    cases v with
    | scalar sc =>
      simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨hsz, hb⟩ := hv
      simpa [TupleSpec.toMiniRustVal, TupleSpec.toMiniRustTy, valToMiniRust] using
        checkValue_valToMiniRust it hgood (.scalar sc) ⟨hsz, hb⟩
    | _ => simp [TupleSpec.valOk] at hv
  | tuple fields size align =>
    cases v with
    | aggregate vidx vals =>
      cases vidx with
      | succ _ => simp [TupleSpec.valOk] at hv
      | zero =>
        simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hv
        obtain ⟨hlen_v, hfwv⟩ := hv
        simp only [TupleSpec.wf, Bool.and_eq_true] at hwf
        obtain ⟨_, hfwf⟩ := hwf
        have hlen_m := TupleSpec.fieldsToMiniRustVal_length fields vals
        have hlen_f := TupleSpec.fieldsToMiniRust_length fields
        have hchk := checkTupleFields_spec size align fields vals hfwf hfwv
        unfold TupleSpec.toMiniRustVal TupleSpec.toMiniRustTy checkValue
        simp [hlen_m, hlen_f, hlen_v, hchk]
    | _ => simp [TupleSpec.valOk] at hv

theorem checkTupleFields_spec (size align : Nat) (fields : List (Nat × TupleSpec))
    (vals : List Value)
    (hfwf : TupleSpec.fieldsWf size align fields = true)
    (hv : TupleSpec.fieldsValOk fields vals = true) :
    checkTupleFields (TupleSpec.fieldsToMiniRustVal fields vals)
      (TupleSpec.fieldsToMiniRust fields) = .ok () := by
  cases fields with
  | nil =>
    cases vals <;> simp [TupleSpec.fieldsValOk] at hv
    simp [TupleSpec.fieldsToMiniRustVal, TupleSpec.fieldsToMiniRust, checkTupleFields]
  | cons f restF =>
    obtain ⟨off, fs⟩ := f
    cases vals with
    | nil => simp [TupleSpec.fieldsValOk] at hv
    | cons v restV =>
      simp only [TupleSpec.fieldsWf, Bool.and_eq_true] at hfwf
      obtain ⟨⟨⟨⟨⟨hfswf, _⟩, _⟩, _⟩, _⟩, hrestWf⟩ := hfwf
      simp only [TupleSpec.fieldsValOk, Bool.and_eq_true] at hv
      obtain ⟨hvv, hrestV⟩ := hv
      have hhead := checkValue_tupleSpec fs v hfswf hvv
      have htail := checkTupleFields_spec size align restF restV hrestWf hrestV
      unfold TupleSpec.fieldsToMiniRustVal TupleSpec.fieldsToMiniRust checkTupleFields
      rw [hhead, except_bind_ok, htail]

end

mutual

theorem encode_tupleSpec (s : TupleSpec) (v : Value)
    (hwf : s.wf = true) (hv : s.valOk v = true) :
    Type.encode s.toMiniRustTy (s.toMiniRustVal v) = .ok (s.encodeVal v) := by
  cases s with
  | scalar it =>
    simp only [TupleSpec.wf] at hwf
    have hgood := (goodAlignBytes_iff it.size.bytes).mp hwf
    cases v with
    | scalar sc =>
      simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨hsz, hb⟩ := hv
      simpa [TupleSpec.toMiniRustTy, TupleSpec.toMiniRustVal, TupleSpec.encodeVal,
        valToMiniRust, valBytes] using
        encode_valToMiniRust it hgood (.scalar sc) ⟨hsz, hb⟩
    | _ => simp [TupleSpec.valOk] at hv
  | tuple fields size align =>
    cases v with
    | aggregate vidx vals =>
      cases vidx with
      | succ _ => simp [TupleSpec.valOk] at hv
      | zero =>
        simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hv
        obtain ⟨hlen_v, hfwv⟩ := hv
        simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
        obtain ⟨⟨⟨_, hmod⟩, _⟩, hfwf⟩ := hwf
        have hlen_m := TupleSpec.fieldsToMiniRustVal_length fields vals
        have hlen_f := TupleSpec.fieldsToMiniRust_length fields
        have henc := encodeTupleFields_spec size align fields vals
          (List.replicate size Gen.AbstractByte.Uninit) hfwf hfwv (by simp)
        unfold TupleSpec.toMiniRustTy TupleSpec.toMiniRustVal TupleSpec.encodeVal Type.encode
        simp [head_size_and_align_mk size align hmod, hlen_m, hlen_f, hlen_v, henc]
    | _ => simp [TupleSpec.valOk] at hv

theorem encodeTupleFields_spec (size align : Nat) (fields : List (Nat × TupleSpec))
    (vals : List Value) (acc : List Byte)
    (hfwf : TupleSpec.fieldsWf size align fields = true)
    (hv : TupleSpec.fieldsValOk fields vals = true)
    (hacc : acc.length = size) :
    encodeTupleFields (TupleSpec.fieldsToMiniRust fields)
        (TupleSpec.fieldsToMiniRustVal fields vals) acc =
      .ok (TupleSpec.encodeFields fields vals acc) := by
  cases fields with
  | nil =>
    cases vals <;> simp [TupleSpec.fieldsValOk] at hv
    simp [TupleSpec.fieldsToMiniRust, TupleSpec.fieldsToMiniRustVal,
      TupleSpec.encodeFields, encodeTupleFields]
  | cons f restF =>
    obtain ⟨off, fs⟩ := f
    cases vals with
    | nil => simp [TupleSpec.fieldsValOk] at hv
    | cons v restV =>
      simp only [TupleSpec.fieldsWf, Bool.and_eq_true, decide_eq_true_eq] at hfwf
      obtain ⟨⟨⟨⟨⟨hfswf, hoff⟩, _⟩, _⟩, _⟩, hrestWf⟩ := hfwf
      simp only [TupleSpec.fieldsValOk, Bool.and_eq_true] at hv
      obtain ⟨hvv, hrestV⟩ := hv
      have hhead := encode_tupleSpec fs v hfswf hvv
      have hlen_e := TupleSpec.encodeVal_length fs v hfswf
      have hw : writeSubsliceAtIndex acc (off : Int) (fs.encodeVal v) =
          .ok (spliceAt acc off (fs.encodeVal v)) :=
        writeSubsliceAtIndex_eq_spliceAt acc off (fs.encodeVal v) (by omega)
      have hacc' : (spliceAt acc off (fs.encodeVal v)).length = size := by
        rw [spliceAt_length _ _ _ (by omega), hacc]
      have htail := encodeTupleFields_spec size align restF restV
        (spliceAt acc off (fs.encodeVal v)) hrestWf hrestV hacc'
      unfold TupleSpec.fieldsToMiniRust TupleSpec.fieldsToMiniRustVal
        TupleSpec.encodeFields encodeTupleFields
      rw [hhead, except_bind_ok, hw, except_bind_ok, htail]

end

/-- Pointer into local `_j` at byte offset `off` (`localPtr ctx j` offset by `off`). -/
def fieldPtr (ctx : Ctx) (j off : Nat) : Ptr :=
  { (localPtr ctx j) with addr := ctx.addrs.getD j 0 + (off : Int) }

@[simp] theorem fieldPtr_zero (ctx : Ctx) (j : Nat) :
    fieldPtr ctx j 0 = localPtr ctx j := by
  simp [fieldPtr, localPtr]

theorem ptrOffsetInbounds_fieldPtr {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (j : Nat) (allocIt : Gen.IntType) (data : List Byte)
    (hL : L[j]? = some (localAlloc ctx j allocIt data))
    (baseOff off : Nat) (hoff : baseOff + off ≤ data.length)
    (hbound : data.length < 2 ^ 63) (haddr0 : 0 ≤ ctx.addrs.getD j 0)
    (haddrMax : ctx.addrs.getD j 0 + (data.length : Int) < 2 ^ 64) :
    ptrOffsetInbounds m (fieldPtr ctx j baseOff) (off : Int) =
      .ok (fieldPtr ctx j (baseOff + off)) := by
  obtain ⟨hj, hLj⟩ := List.getElem?_eq_some_iff.mp hL
  have hderef : CM.signed_dereferenceable m.mem (fieldPtr ctx j baseOff) (off : Int) = .ok () := by
    unfold CM.signed_dereferenceable BM.signed_dereferenceable Size.from_bytes
      BM.dereferenceable BM.check_ptr
    have h0 : 0 ≤ (off : Int) := by omega
    simp only [h0, ↓reduceIte, Int.toNat_natCast]
    by_cases hoff0 : off = 0
    · simp [hoff0]
    · have hle : ¬ ((baseOff : Int) + (off : Int) > (data.length : Int)) := by omega
      simp [hoff0, fieldPtr, localPtr, listIndex, h.allocs, hj, hLj, Allocation.size, hle]
  have hb1 : inBounds (off : Int) .Signed x86_64.PTR_SIZE = true := by
    rw [inBounds_iff _ _ _ (by decide)]
    simp only [windowLo, x86_64.PTR_SIZE, Size.bits]
    omega
  have hb2 : inBounds ((fieldPtr ctx j baseOff).addr + (off : Int)) .Unsigned x86_64.PTR_SIZE = true := by
    rw [inBounds_iff _ _ _ (by decide)]
    simp only [windowLo, x86_64.PTR_SIZE, Size.bits, fieldPtr, localPtr]
    omega
  unfold ptrOffsetInbounds
  rw [hderef, except_bind_ok, hb1, hb2]
  simp [fieldPtr, localPtr, Int.add_assoc]

theorem evalPlace_fieldPath {layouts : Layout.LayoutTable}
    {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (j : Nat) (allocIt : Gen.IntType) (data : List Byte)
    (hL : L[j]? = some (localAlloc ctx j allocIt data))
    (hbound : data.length < 2 ^ 63) (haddr0 : 0 ≤ ctx.addrs.getD j 0)
    (haddrMax : ctx.addrs.getD j 0 + (data.length : Int) < 2 ^ 64)
    (rootPe : Gen.PlaceExpr) (baseOff : Nat) (rootSpec : TupleSpec)
    (hrootEval : evalPlace m rootPe =
      .ok (({ ptr := { thin_pointer := fieldPtr ctx j baseOff, metadata := none },
               aligned := true }, rootSpec.toMiniRustTy), m))
    (hrootWf : rootSpec.wf = true)
    (hbaseBound : baseOff + rootSpec.size ≤ data.length)
    (projs : List ProjectionElem) (pe : Gen.PlaceExpr)
    (hpe : translateFieldPlace rootPe projs = some pe)
    (relOff : Nat) (leafSpec : TupleSpec)
    (hres : resolveFieldPath layouts rootSpec projs = some (relOff, leafSpec)) :
    evalPlace m pe =
      .ok (({ ptr := { thin_pointer := fieldPtr ctx j (baseOff + relOff), metadata := none },
               aligned := true }, leafSpec.toMiniRustTy), m) := by
  induction projs generalizing rootPe baseOff rootSpec relOff with
  | nil =>
    simp [translateFieldPlace] at hpe
    simp [resolveFieldPath] at hres
    subst hpe
    rcases hres with ⟨rfl, rfl⟩
    simpa using hrootEval
  | cons p rest ih =>
    cases p with
    | downcast _ _ => simp [resolveFieldPath] at hres
    | field idx fieldTy =>
      simp only [translateFieldPlace] at hpe
      cases rootSpec with
      | scalar _ => simp [resolveFieldPath] at hres
      | tuple fields size align =>
        simp only [resolveFieldPath, Option.bind_eq_bind] at hres
        cases hf : fields[idx]? with
        | none => simp [hf] at hres
        | some pair =>
          obtain ⟨off, subSpec⟩ := pair
          simp only [hf, Option.bind_some] at hres
          cases hexp : specOfRigidTy layouts fieldTy.kind fieldTy.layoutIdx with
          | none => simp [hexp] at hres
          | some expectedSpec =>
            simp only [hexp, Option.bind_some] at hres
            by_cases heq : subSpec = expectedSpec
            · simp only [heq, ↓reduceIte] at hres
              cases hrest : resolveFieldPath layouts expectedSpec rest with
              | none => simp [hrest] at hres
              | some rpair =>
                obtain ⟨restOff, leafSpec'⟩ := rpair
                simp [hrest] at hres
                rcases hres with ⟨rfl, rfl⟩
                subst heq
                have hrootLay := layout_tupleSpec (.tuple fields size align) hrootWf
                simp only [TupleSpec.wf, Bool.and_eq_true] at hrootWf
                obtain ⟨hsubWf, hoffBound, _, _⟩ := TupleSpec.fieldsWf_getElem? hrootWf.2 hf
                have hsubLay := layout_tupleSpec subSpec hsubWf
                have hgetMr := TupleSpec.fieldsToMiniRust_getElem? fields idx off subSpec hf
                have hidx_lt : idx < (TupleSpec.fieldsToMiniRust fields).length :=
                  (List.getElem?_eq_some_iff.mp hgetMr).1
                have hcond_idx : (0 : Int) ≤ (idx : Int) ∧
                    (idx : Int) < ((TupleSpec.fieldsToMiniRust fields).length : Int) := by
                  exact ⟨by omega, by exact_mod_cast hidx_lt⟩
                have hlidx : listIndex (TupleSpec.fieldsToMiniRust fields) (idx : Int)
                    "sized_fields[field]" = .ok (⟨off⟩, subSpec.toMiniRustTy) := by
                  simp [listIndex, hgetMr]
                have hoff_le_size : off ≤ size := by omega
                simp only [TupleSpec.size] at hbaseBound
                have hptr := ptrOffsetInbounds_fieldPtr h j allocIt data hL baseOff off
                  (by omega) hbound haddr0 haddrMax
                have hstepEval : evalPlace m (.Field rootPe (idx : Int)) =
                    .ok (({ ptr := { thin_pointer := fieldPtr ctx j (baseOff + off), metadata := none },
                             aligned := true }, subSpec.toMiniRustTy), m) := by
                  rw [evalPlace]
                  rw [hrootEval, except_bind_ok]
                  simp only [TupleSpec.toMiniRustTy] at hrootLay ⊢
                  simp only [hcond_idx, and_self, ↓reduceIte, hlidx, except_bind_ok, except_pure,
                    computeSize, hrootLay, LayoutStrategy.compute_size_and_align,
                    TupleSpec.size, hoff_le_size, hptr, hsubLay, LayoutStrategy.is_sized,
                    Bool.not_true, Bool.false_eq_true]
                have hstep := ih (.Field rootPe (idx : Int)) (baseOff + off) subSpec
                  hstepEval hsubWf (by omega) hpe restOff hrest
                simpa [Nat.add_assoc] using hstep
            · simp [heq] at hres
    | _ => simp [translateFieldPlace] at hpe

theorem typedLoad_tuple_slice {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (j : Nat) (allocIt : Gen.IntType) (data : List Byte)
    (hL : L[j]? = some (localAlloc ctx j allocIt data))
    (off : Nat) (subSpec : TupleSpec) (subVal : Value)
    (hwf : subSpec.wf = true) (hv : subSpec.valOk subVal = true)
    (hoff : off + subSpec.size ≤ data.length)
    (hslice : (data.drop off).take subSpec.size = subSpec.encodeVal subVal) :
    ∃ m', typedLoad m (fieldPtr ctx j off) subSpec.toMiniRustTy ⟨1⟩ .None =
        .ok (subSpec.toMiniRustVal subVal, m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  obtain ⟨hj, hLj⟩ := List.getElem?_eq_some_iff.mp hL
  have hlay := layout_tupleSpec subSpec hwf
  have hdec := decode_tupleSpec subSpec subVal hwf hv
  have hck := checkValue_tupleSpec subSpec subVal hwf hv
  have hset := set_self_of_getElem? L j _ hL
  have hload : CM.load m.mem (fieldPtr ctx j off) ⟨subSpec.size⟩ ⟨1⟩ .None =
      .ok (subSpec.encodeVal subVal,
        (withMem m (ctx.base ++ L) ⟨.Load, .None, (fieldPtr ctx j off).addr, ⟨subSpec.size⟩⟩).mem) := by
    by_cases hc : subSpec.size = 0
    · have hlen0 : (subSpec.encodeVal subVal).length = 0 := by
        rw [TupleSpec.encodeVal_length subSpec subVal hwf, hc]
      have hnil : subSpec.encodeVal subVal = [] := List.eq_nil_of_length_eq_zero hlen0
      simp [CM.load, BM.load, BM.check_ptr, hc, hnil, withMem,
        memory_with_allocs_self m.mem.memory _ h.allocs]
    · have hchk2 : ¬ ((data.length : Int) < (off : Int) + (subSpec.size : Int)) := by omega
      have hsub := subsliceWithLength_eq_drop_take data off subSpec.size hoff
      rw [hslice] at hsub
      simp only [CM.load, BM.load, isAligned_one, BM.check_ptr, fieldPtr, localPtr, listIndex, h.allocs]
      simp [hc, hj, hLj, Allocation.size, hchk2, listSet, hsub, hset, withMem]
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, (fieldPtr ctx j off).addr, ⟨subSpec.size⟩⟩,
    ?_, withMem_shape h _⟩
  unfold typedLoad
  rw [hlay]
  simp only [expect_size_sized, except_bind_ok, hload, hdec, hck, except_pure]
  rfl

theorem typedStore_tuple_slice {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (allocIt : Gen.IntType) (data : List Byte)
    (hL : L[i]? = some (localAlloc ctx i allocIt data))
    (off : Nat) (subSpec : TupleSpec) (subVal : Value)
    (hwf : subSpec.wf = true) (hv : subSpec.valOk subVal = true)
    (hoff : off + subSpec.size ≤ data.length) :
    typedStore m (fieldPtr ctx i off) (subSpec.toMiniRustVal subVal) subSpec.toMiniRustTy ⟨1⟩ .None =
      .ok (withMem m (ctx.base ++ L.set i
              (localAlloc ctx i allocIt (spliceAt data off (subSpec.encodeVal subVal))))
            ⟨.Store, .None, (fieldPtr ctx i off).addr, ⟨subSpec.size⟩⟩) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hck := checkValue_tupleSpec subSpec subVal hwf hv
  have henc := encode_tupleSpec subSpec subVal hwf hv
  have hlen_e := TupleSpec.encodeVal_length subSpec subVal hwf
  have hstore : CM.store m.mem (fieldPtr ctx i off) (subSpec.encodeVal subVal) ⟨1⟩ .None =
      .ok (withMem m (ctx.base ++ L.set i
              (localAlloc ctx i allocIt (spliceAt data off (subSpec.encodeVal subVal))))
            ⟨.Store, .None, (fieldPtr ctx i off).addr, ⟨subSpec.size⟩⟩).mem := by
    by_cases hc : subSpec.size = 0
    · have hlen0 : (subSpec.encodeVal subVal).length = 0 := by rw [hlen_e, hc]
      have hnil : subSpec.encodeVal subVal = [] := List.eq_nil_of_length_eq_zero hlen0
      have hsp : spliceAt data off [] = data := by
        unfold spliceAt
        simp
      have hset := set_self_of_getElem? L i _ hL
      simp [CM.store, BM.store, BM.check_ptr, hc, hnil, hsp, hset, withMem,
        memory_with_allocs_self m.mem.memory _ h.allocs]
    · have hchk2 : ¬ ((data.length : Int) < (off : Int) + (subSpec.size : Int)) := by omega
      have hw := writeSubsliceAtIndex_eq_spliceAt data off (subSpec.encodeVal subVal)
        (by rw [hlen_e]; exact hoff)
      simp only [CM.store, BM.store, isAligned_one, BM.check_ptr, hlen_e, hc, ↓reduceIte,
        fieldPtr, localPtr, listIndex, h.allocs]
      simp [hi, hLi, Allocation.size, hchk2, hw, listSet, withMem, localAlloc]
  unfold typedStore
  rw [hck]
  simp only
  rw [henc, except_bind_ok, hstore]
  rfl

/-! ## Operands and rvalues -/

/-- The resolved element index of a projection element on an array of length `count`,
or `none` when evaluating the index is UB (uninitialized index local or out-of-bounds). -/
def projIdx (locals : List LocalSlot) (count : Nat) : ProjectionElem → Option Nat
  | .index idxLocal =>
    match locals[idxLocal]? with
    | some (.init (.scalar sc)) => if sc.bits < count then some sc.bits else none
    | _ => none
  | .constantIndex offset minLength fromEnd =>
    if count < minLength then none
    else
      let idx := if fromEnd then count - offset else offset
      if idx < count then some idx else none
  | _ => none

/-- The bit pattern an Anneal fragment operand evaluates to, or `none` when
reading it is UB (an uninitialized local or out-of-bounds array index). -/
def opBits (locals : List LocalSlot) : Operand → Option Nat
  | .copy ⟨j, []⟩ =>
    match locals[j]? with
    | some (.init (.scalar sc)) => some sc.bits
    | _ => none
  | .copy ⟨j, .field idx fieldTy :: rest⟩ =>
    match locals[j]? with
    | some (.init rootVal) =>
      match readFieldPath rootVal (.field idx fieldTy :: rest) with
      | some (.scalar sc) => some sc.bits
      | _ => none
    | _ => none
  | .copy ⟨j, [proj]⟩ =>
    match locals[j]? with
    | some (.init (.aggregate 0 elems)) =>
      match projIdx locals elems.length proj with
      | some idx =>
        match elems[idx]? with
        | some (.scalar sc) => some sc.bits
        | _ => none
      | none => none
    | _ => none
  | .constant c =>
    match c.val with
    | .scalar (.int sc) => some sc.bits
    | _ => none
  | _ => none

/-- The arithmetic of `eval_int_un_op` for the fragment unary operators. -/
def intUnArith : Gen.IntUnOp → Int → Int
  | .Neg, x => -x
  | .BitNot, x => -x - 1
  | _, _ => 0

theorem evalIntUnOp_eq (uop : MirAst.UnOp) (iuop : Gen.IntUnOp)
    (huop : translateUnOp uop = some iuop) (x : Int) (it : Gen.IntType) :
    evalIntUnOp iuop x it = .ok (IntType.bring_in_bounds it (intUnArith iuop x)) := by
  cases uop <;> simp [translateUnOp] at huop <;> subst huop <;> rfl

theorem intBitRec_zero_right (k : Nat) (x : Int) :
    intBitRec (fun _ => 0) (fun b => b) (fun u v => if u = 1 ∧ v = 1 then 1 else 0) k x 0 = 0 := by
  induction k generalizing x with
  | zero => simp [intBitRec]
  | succ k ih =>
    simp only [intBitRec]
    split
    · rfl
    · split
      · rfl
      · rw [show (0 : Int) / 2 = 0 from rfl, show (0 : Int) % 2 = 0 from rfl, ih (x / 2)]
        omega

/-- On `libspecr::Int`, `x & 1` (`intBitAnd x 1`) equals `x % 2` (`0` or `1`). -/
theorem intBitAnd_one (x : Int) : intBitAnd x 1 = x % 2 := by
  unfold intBitAnd
  have hmod : x % 2 = 0 ∨ x % 2 = 1 := by omega
  cases hk : intBitMeasure x with
  | zero =>
    simp only [intBitRec]
    split
    · next h0 => subst h0; rfl
    · next hne0 =>
      have hx1 : x = -1 := by
        unfold intBitMeasure at hk
        split at hk <;> omega
      subst hx1; rfl
  | succ k =>
    simp only [intBitRec]
    split
    · next h0 => subst h0; rfl
    · split
      · next hn1 => subst hn1; rfl
      · rw [show (1 : Int) / 2 = 0 from rfl, show (1 : Int) % 2 = 1 from rfl,
          intBitRec_zero_right k (x / 2)]
        rcases hmod with hmod | hmod <;> simp [hmod]

theorem countOnesLoop_bounds (n : Nat) (acc x : Int) :
    acc ≤ countOnesLoop n acc x ∧ countOnesLoop n acc x ≤ acc + n := by
  induction n generalizing acc x with
  | zero => simp [countOnesLoop]
  | succ n ih =>
    simp only [countOnesLoop, intBitAnd_one]
    have hmod : 0 ≤ x % 2 ∧ x % 2 ≤ 1 := by omega
    have ⟨hl, hr⟩ := ih (acc + x % 2) (x / 2)
    omega

/-- `Machine::eval_un_op` on `UnOp::Int(IntUnOp::CountOnes)` never triggers the
`check_value` sanity-check panic on any `GoodSize` integer type, returning
`evalCountOnes x it` at type `u32` (`spec/lang/step/operators.md`). -/
theorem evalUnOp_countOnes (x : Int) (it : Gen.IntType) (hgood : GoodSize it.size.bytes) :
    evalUnOp (.Int .CountOnes) (.Int x, .Int it) =
      .ok (.Int (evalCountOnes x it), .Int ⟨.Unsigned, ⟨4⟩⟩) := by
  have hb := countOnesLoop_bounds (Size.bits it.size) 0 x
  have hbits : (Size.bits it.size : Int) < (2 : Int) ^ Size.bits ⟨4⟩ := by
    unfold Size.bits
    rcases hgood with h | h | h | h | h <;> rw [h] <;> decide
  have hrep : IntType.can_represent ⟨.Unsigned, ⟨4⟩⟩ (evalCountOnes x it) = true := by
    unfold IntType.can_represent inBounds evalCountOnes
    dsimp only
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    omega
  simp [evalUnOp, evalIntUnOp, checkValue, hrep]

/-- Symbolic characterization of `Machine::eval_int_bin_op` on `IntBinOp::DivExact`
(`spec/lang/step/operators.md`):
* `r = 0` raises `.ub "division by zero"`,
* `r ≠ 0` and `!IntType.can_represent it (Int.tdiv l r)` raises `.ub "overflow in division"`,
* `r ≠ 0`, `IntType.can_represent it (Int.tdiv l r) = true`, and `Int.tmod l r ≠ 0`
  raises `.ub "non-zero remainder in exact division"`, and
* otherwise returns `.ok (Int.tdiv l r)`. -/
theorem evalIntBinOp_divExact (l r : Int) (it : Gen.IntType) :
    evalIntBinOp .DivExact l r it =
      if r = 0 then .error (.ub "division by zero")
      else if !IntType.can_represent it (Int.tdiv l r) then .error (.ub "overflow in division")
      else if Int.tmod l r ≠ 0 then .error (.ub "non-zero remainder in exact division")
      else .ok (Int.tdiv l r) := by
  rfl

theorem intUnArith_emod (uop : MirAst.UnOp) (iuop : Gen.IntUnOp)
    (huop : translateUnOp uop = some iuop) (x x' m : Int) (hx : x % m = x' % m) :
    intUnArith iuop x % m = intUnArith iuop x' % m := by
  cases uop <;> simp [translateUnOp] at huop <;> subst huop <;> simp only [intUnArith]
  · rw [show -x - 1 = -1 - x by omega, show -x' - 1 = -1 - x' by omega,
      Int.sub_emod, hx, ← Int.sub_emod]
  · rw [show -x = 0 - x by omega, show -x' = 0 - x' by omega,
      Int.sub_emod, hx, ← Int.sub_emod]

/-- Partial integer evaluation of `eval_int_bin_op` for the fragment binary
operators: returns `some z` when `evalIntBinOp iop l r it = .ok z` and `none`
when `evalIntBinOp` raises UB (`throw_ub!`). -/
def intBinEval (iop : Gen.IntBinOp) (l r : Int) (it : Gen.IntType) : Option Int :=
  match iop with
  | .Add => some (l + r)
  | .Sub => some (l - r)
  | .Mul => some (l * r)
  | .AddUnchecked => if IntType.can_represent it (l + r) then some (l + r) else none
  | .SubUnchecked => if IntType.can_represent it (l - r) then some (l - r) else none
  | .MulUnchecked => if IntType.can_represent it (l * r) then some (l * r) else none
  | .Div =>
    if r = 0 then none
    else if IntType.can_represent it (Int.tdiv l r) then some (Int.tdiv l r)
    else none
  | .Rem =>
    if r = 0 then none
    else if IntType.can_represent it (Int.tdiv l r) then some (Int.tmod l r)
    else none
  | .Shl =>
    let bits : Int := Size.bits it.size
    some (l * (2 : Int) ^ (r % bits).toNat)
  | .Shr =>
    let bits : Int := Size.bits it.size
    some (l / (2 : Int) ^ (r % bits).toNat)
  | .ShlUnchecked =>
    let bits : Int := Size.bits it.size
    if r < 0 ∨ r ≥ bits then none else some (l * (2 : Int) ^ r.toNat)
  | .ShrUnchecked =>
    let bits : Int := Size.bits it.size
    if r < 0 ∨ r ≥ bits then none else some (l / (2 : Int) ^ r.toNat)
  | .BitAnd => some (intBitAnd l r)
  | .BitOr => some (intBitOr l r)
  | .BitXor => some (intBitXor l r)
  | _ => none

theorem evalIntBinOp_spec (op : MirAst.BinOp) (iop : Gen.IntBinOp)
    (hop : translateBinOp op = some iop) (l r : Int) (it : Gen.IntType) :
    (∀ z, intBinEval iop l r it = some z → evalIntBinOp iop l r it = .ok z) ∧
    (intBinEval iop l r it = none → ∃ msg, evalIntBinOp iop l r it = .error (.ub msg)) := by
  match op, hop with
  | .add, hop | .sub, hop | .mul, hop | .bitXor, hop | .bitAnd, hop | .bitOr, hop
  | .shl, hop | .shr, hop =>
    simp [translateBinOp] at hop; subst hop; simp [intBinEval, evalIntBinOp]
  | .addUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    cases hrep : IntType.can_represent it (l + r) <;> simp [intBinEval, evalIntBinOp, hrep, ub]
  | .subUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    cases hrep : IntType.can_represent it (l - r) <;> simp [intBinEval, evalIntBinOp, hrep, ub]
  | .mulUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    cases hrep : IntType.can_represent it (l * r) <;> simp [intBinEval, evalIntBinOp, hrep, ub]
  | .div, hop =>
    simp [translateBinOp] at hop; subst hop
    by_cases hr0 : r = 0
    · simp [intBinEval, evalIntBinOp, hr0, ub]
    · cases hrep : IntType.can_represent it (Int.tdiv l r) <;>
        simp [intBinEval, evalIntBinOp, hr0, hrep, ub]
  | .rem, hop =>
    simp [translateBinOp] at hop; subst hop
    by_cases hr0 : r = 0
    · simp [intBinEval, evalIntBinOp, hr0, ub]
    · cases hrep : IntType.can_represent it (Int.tdiv l r) <;>
        simp [intBinEval, evalIntBinOp, hr0, hrep, ub]
  | .shlUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    by_cases hoob : r < 0 ∨ r ≥ Size.bits it.size <;> simp [intBinEval, evalIntBinOp, hoob, ub]
  | .shrUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    by_cases hoob : r < 0 ∨ r ≥ Size.bits it.size <;> simp [intBinEval, evalIntBinOp, hoob, ub]

theorem operandIntType_of_operandOk {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {it : Gen.IntType} {op : Operand}
    (h : operandOk layouts decls it op = true) : operandIntType layouts decls op = some it := by
  match op, h with
  | .copy ⟨_, []⟩, h =>
    simp only [operandOk, placeOk, operandIntType, placeIntType,
      Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact h.1.2
  | .copy ⟨j, proj :: rest⟩, h =>
    cases proj with
    | field idx fieldTy =>
      simp only [operandOk, placeOk, operandIntType, placeIntType,
        Bool.and_eq_true] at h ⊢
      obtain ⟨⟨_, hok⟩, _⟩ := h
      cases hd : decls[j]? with
      | none => simp [hd] at hok
      | some d =>
        simp only [hd, Option.bind_eq_bind, Option.bind_some] at hok ⊢
        cases ht : tupleTypeOf layouts d.ty with
        | none => simp [ht] at hok
        | some p =>
          obtain ⟨fields, size, align⟩ := p
          simp only [ht, Option.bind_some] at hok ⊢
          cases hres : resolveFieldPath layouts (.tuple fields size align)
              (.field idx fieldTy :: rest) with
          | none => simp [hres] at hok
          | some rpair =>
            obtain ⟨_, leafSpec⟩ := rpair
            simp only [hres, Option.bind_some] at hok ⊢
            cases leafSpec with
            | scalar leafIt =>
              simp only [decide_eq_true_eq] at hok
              subst hok
              rfl
            | tuple _ _ _ => simp at hok
    | index idxLocal =>
      cases rest with
      | nil =>
        simp only [operandOk, placeOk, operandIntType, placeIntType,
          Bool.and_eq_true, decide_eq_true_eq] at h ⊢
        obtain ⟨⟨_, hok⟩, _⟩ := h
        cases hd : decls[j]? with
        | none => simp [hd] at hok
        | some d =>
          simp only [hd, Option.bind_eq_bind, Option.bind_some] at hok ⊢
          cases ha : arrayTypeOf d.ty with
          | none => simp [ha] at hok
          | some p =>
            obtain ⟨elemIt, count⟩ := p
            simp only [ha, Bool.and_eq_true, decide_eq_true_eq, Option.map_some, Option.some.injEq] at hok ⊢
            exact hok.1
      | cons _ _ => simp [operandOk, translateOperand, translatePlace, placeOk] at h
    | constantIndex offset minLen fromEnd =>
      cases rest with
      | nil =>
        simp only [operandOk, placeOk, operandIntType, placeIntType,
          Bool.and_eq_true, decide_eq_true_eq] at h ⊢
        obtain ⟨⟨_, hok⟩, _⟩ := h
        cases hd : decls[j]? with
        | none => simp [hd] at hok
        | some d =>
          simp only [hd, Option.bind_eq_bind, Option.bind_some] at hok ⊢
          cases ha : arrayTypeOf d.ty with
          | none => simp [ha] at hok
          | some p =>
            obtain ⟨elemIt, count⟩ := p
            simp only [ha, Bool.and_eq_true, decide_eq_true_eq, Option.map_some, Option.some.injEq] at hok ⊢
            exact hok.1
      | cons _ _ => simp [operandOk, translateOperand, translatePlace, placeOk] at h
    | _ => cases rest <;> simp [operandOk, translateOperand, translatePlace, placeOk, projOk] at h <;> try split at h <;> try cases h <;> try rename_i left right <;> try cases left <;> try simp_all
  | .constant _, h =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

theorem rvalueOk_binaryOp {layouts : Layout.LayoutTable} {decls : List LocalDecl} {it : Gen.IntType}
    {op : MirAst.BinOp} {a b : Operand}
    (h : rvalueOk layouts decls it (.binaryOp op a b) = true) :
    ∃ iop rhsIt,
      translateBinOp op = some iop ∧
      operandOk layouts decls it a = true ∧
      operandIntType layouts decls b = some rhsIt ∧
      operandOk layouts decls rhsIt b = true ∧
      (isShiftIntBinOp iop = false → rhsIt = it) := by
  simp only [rvalueOk] at h
  cases hiop : translateBinOp op with
  | none => simp [hiop] at h
  | some iop =>
    simp only [hiop, Bool.and_eq_true] at h
    obtain ⟨hoka, hokb⟩ := h
    cases hsh : isShiftIntBinOp iop with
    | true =>
      simp only [hsh, ↓reduceIte] at hokb
      cases hrhs : operandIntType layouts decls b with
      | none => simp [hrhs] at hokb
      | some rhsIt =>
        simp only [hrhs] at hokb
        exact ⟨iop, rhsIt, rfl, hoka, rfl, hokb, fun hf => by rw [hsh] at hf; cases hf⟩
    | false =>
      simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hokb
      exact ⟨iop, it, rfl, hoka, operandIntType_of_operandOk hokb, hokb, fun _ => rfl⟩

/-- Hypotheses describing a callee frame related to Anneal locals `locals`. -/
structure FrameOk (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (locals : List LocalSlot)
    (m : Mach) (blk stmt : Nat) : Prop where
  hf : translateFn body = some f
  shape : Shape m ctx [ctx.caller, calleeFrame f ctx body.localDecls.length blk stmt]
    (ctx.base ++ localAllocs body.layouts ctx body.localDecls locals)
  nlocals : locals.length = body.localDecls.length
  slots : ∀ (i : Nat) d slot, body.localDecls[i]? = some d → locals[i]? = some slot →
    DeclSlotOk body.layouts d slot
  addrs : ∀ (i : Nat) d, body.localDecls[i]? = some d → AddrOk body.layouts (ctx.addrs.getD i 0) d
  declsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true

theorem FrameOk.decl_good {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {locals : List LocalSlot}
    {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt) (i : Nat) (d : LocalDecl)
    (hd : body.localDecls[i]? = some d) : GoodSize (itOf body.layouts d).size.bytes := by
  have hdok := h.declsOk d (List.mem_of_getElem? hd)
  simp only [localDeclOk] at hdok
  unfold itOf
  cases ha : arrayTypeOf d.ty with
  | none =>
    cases ht : tupleTypeOf body.layouts d.ty with
    | none =>
      cases hit : intTypeOf d.ty with
      | none => simp [ha, ht, hit] at hdok
      | some it => exact intTypeOf_good hit
    | some p =>
      obtain ⟨fields, size, align⟩ := p
      have hnone := intTypeOf_none_of_tupleTypeOf ht
      simp only [hnone, Option.isSome_none, Bool.false_or, ha, ht,
        TupleSpec.wf, Bool.and_eq_true] at hdok
      exact (goodAlignBytes_iff align).mp hdok.1.1.1
  | some p =>
    exact arrayTypeOf_good ha

theorem FrameOk.array_bound {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {locals : List LocalSlot}
    {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt) (i : Nat) (d : LocalDecl)
    (elemIt : Gen.IntType) (count : Nat) (hd : body.localDecls[i]? = some d)
    (ha : arrayTypeOf d.ty = some (elemIt, count)) : count * elemIt.size.bytes < 2 ^ 63 := by
  have hdok := h.declsOk d (List.mem_of_getElem? hd)
  have hnone := intTypeOf_none_of_arrayTypeOf ha
  simpa [localDeclOk, hnone, ha] using hdok

theorem FrameOk.tuple_wf {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {locals : List LocalSlot}
    {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt) (i : Nat) (d : LocalDecl)
    (fields : List (Nat × TupleSpec)) (size align : Nat) (hd : body.localDecls[i]? = some d)
    (ht : tupleTypeOf body.layouts d.ty = some (fields, size, align)) :
    (TupleSpec.tuple fields size align).wf = true := by
  have hdok := h.declsOk d (List.mem_of_getElem? hd)
  have hnone1 := intTypeOf_none_of_tupleTypeOf ht
  have hnone2 := arrayTypeOf_none_of_tupleTypeOf ht
  simpa [localDeclOk, hnone1, hnone2, ht] using hdok

theorem FrameOk.localAllocs_get {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (_h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (slot : LocalSlot) (hd : body.localDecls[i]? = some d)
    (hs : locals[i]? = some slot) :
    (localAllocs body.layouts ctx body.localDecls locals)[i]? =
      some (localAlloc ctx i (itOf body.layouts d) (declSlotData body.layouts d slot)) := by
  simpa [localAllocs] using localAllocsFrom_getElem? body.layouts ctx 0 body.localDecls locals i d slot hd hs

theorem FrameOk.slot_exists {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (hi : i < body.localDecls.length) :
    ∃ d slot, body.localDecls[i]? = some d ∧ locals[i]? = some slot := by
  refine ⟨body.localDecls[i], locals[i]'(by rw [h.nlocals]; exact hi), by simp [hi], by simp⟩

/-- Evaluating a translated array projection place `arr[proj]`. -/
theorem evalPlace_proj {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (j : Nat) (d : LocalDecl) (hd : body.localDecls[j]? = some d)
    (elemIt : Gen.IntType) (count : Nat) (ha : arrayTypeOf d.ty = some (elemIt, count))
    (proj : ProjectionElem) (hproj : projOk body.localDecls count proj = true)
    (pe : Gen.PlaceExpr) (hpe : translatePlace body.localDecls ⟨j, [proj]⟩ = some pe) :
    (∀ idx, projIdx locals count proj = some idx →
      idx < count ∧
      ∃ m', evalPlace m pe = .ok (({ ptr := { thin_pointer := elemPtr ctx j idx elemIt, metadata := none },
                                     aligned := true }, .Int elemIt), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (projIdx locals count proj = none → ∃ msg, evalPlace m pe = .error (.ub msg)) := by
  have hj : j < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood := arrayTypeOf_good ha
  have hbound := h.array_bound j d elemIt count hd ha
  have htr : translateTy body.layouts d.ty = some (.Array (.Int elemIt) (count : Int)) := by
    simp [translateTy, intTypeOf_none_of_arrayTypeOf ha, ha]
  have hspec := translateFn_local_ty h.hf j d _ hd htr
  have hplaceBase := evalPlace_local h.shape j hj _ hspec
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists j hj
  have hslot := h.slots j d slot hd hs
  have hL := h.localAllocs_get j d slot hd hs
  have hdlen := declSlotData_length d slot hslot
  simp only [ha] at hdlen
  have haddr := h.addrs j d hd
  simp only [AddrOk, ha] at haddr
  obtain ⟨_, haddr0, haddrMax⟩ := haddr
  have hitd : itOf body.layouts d = elemIt := by simp [itOf, ha]
  match proj, hproj, hpe with
  | .index idxLocal, hproj, hpe =>
    simp only [translatePlace, Option.some.injEq] at hpe
    subst hpe
    simp only [projOk, Bool.and_eq_true, decide_eq_true_eq] at hproj
    obtain ⟨hidxLt, hproj⟩ := hproj
    cases hdIdx : body.localDecls[idxLocal]? with
    | none => simp [hdIdx] at hproj
    | some idxDecl =>
      simp only [hdIdx, Option.bind_eq_bind, Option.bind_some] at hproj
      cases hitIdx : intTypeOf idxDecl.ty with
      | none => simp [hitIdx] at hproj
      | some idxIt =>
        simp only [hitIdx, decide_eq_true_eq] at hproj
        obtain ⟨_, idxSlot, hdIdx', hslotIdx⟩ := h.slot_exists idxLocal hidxLt
        rw [hdIdx] at hdIdx'; cases hdIdx'
        have harrNone := arrayTypeOf_none_of_intTypeOf hitIdx
        have htupNone := tupleTypeOf_none_of_intTypeOf (layouts := body.layouts) hitIdx
        have hitdIdx : itOf body.layouts idxDecl = idxIt := by simp [itOf, harrNone, htupNone, hitIdx]
        have htrIdx : translateTy body.layouts idxDecl.ty = some (.Int idxIt) := by
          simp [translateTy, hitIdx]
        have hspecIdx := translateFn_local_ty h.hf idxLocal idxDecl _ hdIdx htrIdx
        have hplaceIdx := evalPlace_local h.shape idxLocal hidxLt _ hspecIdx
        have hgoodIdx := intTypeOf_good hitIdx
        have hLIdx := h.localAllocs_get idxLocal idxDecl idxSlot hdIdx hslotIdx
        simp only [declSlotData, harrNone, htupNone] at hLIdx
        rw [hitdIdx] at hLIdx
        have hslotIdxOk := h.slots idxLocal idxDecl idxSlot hdIdx hslotIdx
        simp only [DeclSlotOk, harrNone, htupNone] at hslotIdxOk
        rw [hitdIdx] at hslotIdxOk
        match idxSlot, hslotIdxOk, hLIdx with
        | .uninit, _, hLIdx =>
          refine ⟨fun idx hidx => by simp [projIdx, hslotIdx] at hidx, fun _ => ?_⟩
          obtain ⟨msg, hmsg⟩ :=
            typedLoad_local_uninit h.shape idxLocal idxIt hgoodIdx hLIdx ⟨1⟩ (isAligned_one _)
          refine ⟨msg, ?_⟩
          rw [evalPlace]
          simp [hplaceBase, evalValue, hplaceIdx, placeLoad, hmsg]
        | .init (.scalar sc), ⟨_, hscBits⟩, hLIdx =>
          obtain ⟨m1, hm1, hshape1⟩ :=
            typedLoad_local_init h.shape idxLocal idxIt sc.bits hgoodIdx hscBits hLIdx ⟨1⟩ (isAligned_one _)
          have h1 : FrameOk body f ctx locals m1 blk stmt :=
            ⟨h.hf, hshape1, h.nlocals, h.slots, h.addrs, h.declsOk⟩
          by_cases hlt : sc.bits < count
          · refine ⟨fun idx hidx => ?_, fun hnone => by simp [projIdx, hslotIdx, hlt] at hnone⟩
            simp only [projIdx, hslotIdx, hlt, ↓reduceIte, Option.some.injEq] at hidx
            subst hidx
            have hib : intFromBits sc.bits idxIt = (sc.bits : Int) := by
              rcases hproj with huns | hcnt
              · simp [intFromBits, huns]
              · unfold intFromBits
                split
                · rfl
                · have : ¬ (sc.bits ≥ 2 ^ (8 * idxIt.size.bytes - 1)) := by omega
                  simp [this]
            have hnot_le : ¬ (count ≤ sc.bits) := Nat.not_le.mpr hlt
            have hoff_le : sc.bits * elemIt.size.bytes ≤ (declSlotData body.layouts d slot).length := by
              rw [hdlen]
              exact Nat.mul_le_mul_right _ (by omega)
            have hoff_bound : sc.bits * elemIt.size.bytes < 2 ^ 63 := by
              have : sc.bits * elemIt.size.bytes ≤ count * elemIt.size.bytes :=
                Nat.mul_le_mul_right _ (by omega)
              omega
            have hL1 := h1.localAllocs_get j d slot hd hs
            rw [hitd] at hL1
            have hptr := ptrOffsetInbounds_elem h1.shape j sc.bits elemIt (declSlotData body.layouts d slot) hL1
              hoff_le hoff_bound haddr0 (by rw [hdlen]; exact haddrMax)
            have hsz : ¬ (count * elemIt.size.bytes < sc.bits * elemIt.size.bytes) :=
              Nat.not_lt.mpr (Nat.mul_le_mul_right _ (by omega))
            refine ⟨hlt, m1, ?_, h1⟩
            rw [evalPlace]
            simp [hplaceBase, evalValue, hplaceIdx, placeLoad, hm1, hib, hnot_le,
              layout_eq _ hgood, layout_array_eq _ _ hgood, computeSize,
              LayoutStrategy.compute_size_and_align, hsz, hptr]
          · refine ⟨fun idx hidx => by simp [projIdx, hslotIdx, hlt] at hidx, fun _ => ?_⟩
            have hoob : intFromBits sc.bits idxIt < 0 ∨ intFromBits sc.bits idxIt ≥ (count : Int) := by
              unfold intFromBits
              split
              · right; omega
              · split
                · right; omega
                · left
                  have : (sc.bits : Int) < (2 : Int) ^ (8 * idxIt.size.bytes) := by exact_mod_cast hscBits
                  omega
            refine ⟨"access to out-of-bounds index", ?_⟩
            rw [evalPlace]
            simp [hplaceBase, evalValue, hplaceIdx, placeLoad, hm1, hoob, ub]
  | .constantIndex offset minLength fromEnd, hproj, hpe =>
    simp only [projOk, Bool.and_eq_true, decide_eq_true_eq] at hproj
    obtain ⟨⟨hmin, hoffBound⟩, hfe⟩ := hproj
    have hcond : minLength ≤ count ∧ (!fromEnd = true ∨ 1 ≤ offset ∧ offset ≤ count) := by
      refine ⟨hmin, ?_⟩
      cases fromEnd <;> simp at hfe ⊢
      exact hfe
    simp only [translatePlace, hd, Option.bind_eq_bind, Option.bind_some, ha,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hpe
    have hcond' : minLength ≤ count ∧ (fromEnd = false ∨ 1 ≤ offset ∧ offset ≤ count) := by
      simpa using hcond
    simp [hcond'] at hpe
    subst hpe
    have hnot_min : ¬ (count < minLength) := by omega
    generalize hidx_eq : (if fromEnd = true then count - offset else offset) = idx
    by_cases hidx_lt : idx < count
    · refine ⟨fun idx' hidx' => ?_, fun hnone => by simp [projIdx, hnot_min, hidx_eq, hidx_lt] at hnone⟩
      simp only [projIdx, hnot_min, ↓reduceIte, hidx_eq, hidx_lt, Option.some.injEq] at hidx'
      subst hidx'
      have hnot_le : ¬ (count ≤ idx) := Nat.not_le.mpr hidx_lt
      have hoff_le : idx * elemIt.size.bytes ≤ (declSlotData body.layouts d slot).length := by
        rw [hdlen]
        exact Nat.mul_le_mul_right _ (by omega)
      have hoff_bound : idx * elemIt.size.bytes < 2 ^ 63 := by
        have : idx * elemIt.size.bytes ≤ count * elemIt.size.bytes :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      rw [hitd] at hL
      have hptr := ptrOffsetInbounds_elem h.shape j idx elemIt (declSlotData body.layouts d slot) hL
        hoff_le hoff_bound haddr0 (by rw [hdlen]; exact haddrMax)
      have hsz : ¬ (count * elemIt.size.bytes < idx * elemIt.size.bytes) :=
        Nat.not_lt.mpr (Nat.mul_le_mul_right _ (by omega))
      refine ⟨hidx_lt, m, ?_, h⟩
      rw [evalPlace]
      simp [hplaceBase, evalValue, evalConstant, hnot_le, layout_eq _ hgood,
        layout_array_eq _ _ hgood, computeSize, LayoutStrategy.compute_size_and_align, hsz,
        hptr]
    · refine ⟨fun idx' hidx' => by simp [projIdx, hnot_min, hidx_eq, hidx_lt] at hidx', fun _ => ?_⟩
      have hle_cnt : count ≤ idx := Nat.le_of_not_lt hidx_lt
      refine ⟨"access to out-of-bounds index", ?_⟩
      rw [evalPlace]
      simp [hplaceBase, evalValue, evalConstant, hle_cnt, ub]

theorem placeOk_single_nonfield {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {it : Gen.IntType} {j : Nat} {proj : ProjectionElem}
    (hnf : ∀ idx fieldTy, proj ≠ .field idx fieldTy) :
    placeOk layouts decls it ⟨j, [proj]⟩ =
      (decide (j < decls.length) &&
        match decls[j]?.bind (fun d => arrayTypeOf d.ty) with
        | some (elemIt, count) => decide (elemIt = it) && projOk decls count proj
        | none => false) := by
  cases proj with
  | field idx fieldTy => exact False.elim (hnf idx fieldTy rfl)
  | downcast _ _ => simp [placeOk]; cases decls[j]?.bind fun d => arrayTypeOf d.ty <;> simp [projOk]
  | _ => rfl

theorem evalValue_operand_array_proj {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (it : Gen.IntType) (j : Nat) (proj : ProjectionElem)
    (hnf : ∀ idx fieldTy, proj ≠ .field idx fieldTy)
    (hok : operandOk body.layouts body.localDecls it (.copy ⟨j, [proj]⟩) = true)
    (e : Gen.ValueExpr) (he : translateOperand body.localDecls (.copy ⟨j, [proj]⟩) = some e) :
    (∀ bits, opBits locals (.copy ⟨j, [proj]⟩) = some bits →
      bits < 2 ^ (8 * it.size.bytes) ∧
      ∃ m', evalValue m e = .ok ((.Int (intFromBits bits it), .Int it), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (opBits locals (.copy ⟨j, [proj]⟩) = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  simp only [operandOk, placeOk_single_nonfield hnf, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hj, hok⟩, _⟩ := hok
  cases hd : body.localDecls[j]? with
  | none => simp [hd] at hok
  | some d =>
    simp only [hd, Option.bind_some] at hok
    cases ha : arrayTypeOf d.ty with
    | none => simp [ha] at hok
    | some p =>
      obtain ⟨elemIt, count⟩ := p
      simp only [ha, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨helemEq, hproj⟩ := hok
      subst helemEq
      simp only [translateOperand] at he
      cases hpe : translatePlace body.localDecls ⟨j, [proj]⟩ with
      | none => simp [hpe] at he
      | some pe =>
        simp only [hpe, Option.map_some, Option.some.injEq] at he
        subst he
        obtain ⟨hpok, hpnone⟩ := evalPlace_proj h j d hd elemIt count ha proj hproj pe hpe
        obtain ⟨_, slot, hd', hs⟩ := h.slot_exists j hj
        rw [hd] at hd'; cases hd'
        have hslot := h.slots j d slot hd hs
        simp only [DeclSlotOk, ha] at hslot
        have hL := h.localAllocs_get j d slot hd hs
        have hitd : itOf body.layouts d = elemIt := by simp [itOf, ha]
        rw [hitd] at hL
        simp only [declSlotData, ha] at hL
        have hgood := arrayTypeOf_good ha
        match slot, hslot, hL with
        | .init (.aggregate 0 elems), ⟨hlen, he⟩, hL =>
          cases hidx : projIdx locals count proj with
          | none =>
            refine ⟨fun bits hbits => by simp [opBits, hs, hlen, hidx] at hbits, fun _ => ?_⟩
            obtain ⟨msg, hmsg⟩ := hpnone hidx
            exact ⟨msg, by simp [evalValue, hmsg]⟩
          | some idx =>
            obtain ⟨hidx_lt, m1, hm1, h1⟩ := hpok idx hidx
            have hL1 := h1.localAllocs_get j d (.init (.aggregate 0 elems)) hd hs
            rw [hitd] at hL1
            simp only [declSlotData, ha] at hL1
            have hget : ∃ sc, elems[idx]? = some (.scalar sc) := by
              have hex : ∃ v, elems[idx]? = some v :=
                ⟨elems[idx]'(by omega), List.getElem?_eq_getElem (by omega)⟩
              obtain ⟨v, hv⟩ := hex
              have hvok := he v (List.mem_of_getElem? hv)
              cases v with
              | scalar sc => exact ⟨sc, hv⟩
              | _ => exact False.elim hvok
            obtain ⟨sc, hsc⟩ := hget
            obtain ⟨_, hb⟩ := he (.scalar sc) (List.mem_of_getElem? hsc)
            obtain ⟨m2, hm2, hshape2⟩ := typedLoad_array_elem h1.shape j idx elemIt count
              elems sc hgood hlen he hsc hL1
            refine ⟨fun bits hbits => ?_, fun hnone => ?_⟩
            · simp [opBits, hs, hlen, hidx, hsc] at hbits
              subst hbits
              exact ⟨hb, m2, by simp [evalValue, hm1, placeLoad, hm2],
                ⟨h.hf, hshape2, h.nlocals, h.slots, h.addrs, h.declsOk⟩⟩
            · simp [opBits, hs, hlen, hidx, hsc] at hnone

/-- Evaluating a translated fragment operand. -/
theorem evalValue_operand {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (it : Gen.IntType) (op : Operand) (hok : operandOk body.layouts body.localDecls it op = true)
    (e : Gen.ValueExpr) (he : translateOperand body.localDecls op = some e) :
    (∀ bits, opBits locals op = some bits →
      bits < 2 ^ (8 * it.size.bytes) ∧
      ∃ m', evalValue m e = .ok ((.Int (intFromBits bits it), .Int it), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (opBits locals op = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  match op, hok, he with
  | .copy ⟨j, []⟩, hok, he =>
    simp only [operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hj, hty⟩, _⟩ := hok
    simp only [translateOperand, translatePlace, Option.map_some,
      Option.some.injEq] at he
    subst he
    obtain ⟨d, slot, hd, hs⟩ := h.slot_exists j hj
    rw [hd] at hty
    simp only [Option.bind_eq_bind, Option.bind_some] at hty
    have harrNone := arrayTypeOf_none_of_intTypeOf hty
    have htupNone := tupleTypeOf_none_of_intTypeOf (layouts := body.layouts) hty
    have hit : itOf body.layouts d = it := by simp [itOf, harrNone, htupNone, hty]
    subst hit
    have htr : translateTy body.layouts d.ty = some (.Int (itOf body.layouts d)) := by
      simp [translateTy, hty]
    have hspec := translateFn_local_ty h.hf j d _ hd htr
    have hplace := evalPlace_local h.shape j hj _ hspec
    have hgood := h.decl_good j d hd
    have hL := h.localAllocs_get j d slot hd hs
    simp only [declSlotData, harrNone, htupNone] at hL
    have hslot := h.slots j d slot hd hs
    simp only [DeclSlotOk, harrNone, htupNone] at hslot
    match slot, hslot, hL with
    | .uninit, _, hL =>
      refine ⟨fun bits hb => by simp [opBits, hs] at hb, fun _ => ?_⟩
      obtain ⟨msg, hmsg⟩ := typedLoad_local_uninit h.shape j (itOf body.layouts d) hgood hL ⟨1⟩ (isAligned_one _)
      exact ⟨msg, by simp [evalValue, hplace, placeLoad, hmsg]⟩
    | .init (.scalar sc), hok', hL =>
      obtain ⟨_, hb⟩ := hok'
      refine ⟨fun bits hbits => ?_, fun hnone => by simp [opBits, hs] at hnone⟩
      simp [opBits, hs] at hbits
      subst hbits
      obtain ⟨m', hm', hshape⟩ :=
        typedLoad_local_init h.shape j (itOf body.layouts d) sc.bits hgood hb hL ⟨1⟩ (isAligned_one _)
      exact ⟨hb, m', by simp [evalValue, hplace, placeLoad, hm'],
        ⟨h.hf, hshape, h.nlocals, h.slots, h.addrs, h.declsOk⟩⟩
  | .copy ⟨j, .field idx fieldTy :: rest⟩, hok, he =>
    simp only [operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hj, hok⟩, _⟩ := hok
    cases hd : body.localDecls[j]? with
    | none => simp [hd] at hok
    | some d =>
      simp only [hd, Option.bind_eq_bind, Option.bind_some] at hok
      cases ht : tupleTypeOf body.layouts d.ty with
      | none => simp [ht] at hok
      | some p =>
        obtain ⟨fields, size, align⟩ := p
        simp only [ht] at hok
        cases hres : resolveFieldPath body.layouts (.tuple fields size align)
            (.field idx fieldTy :: rest) with
        | none => simp [hres] at hok
        | some rpair =>
          obtain ⟨relOff, leafSpec⟩ := rpair
          simp only [hres] at hok
          cases leafSpec with
          | tuple _ _ _ => simp at hok
          | scalar leafIt =>
            simp only [decide_eq_true_eq] at hok
            subst hok
            simp only [translateOperand, translatePlace] at he
            cases hpe : translateFieldPlace (.Local (localName j))
                (.field idx fieldTy :: rest) with
            | none => simp [hpe] at he
            | some pe =>
              simp only [hpe, Option.map_some, Option.some.injEq] at he
              subst he
              obtain ⟨_, slot, hd', hs⟩ := h.slot_exists j hj
              rw [hd] at hd'; cases hd'
              have hnone1 := intTypeOf_none_of_tupleTypeOf ht
              have hnone2 := arrayTypeOf_none_of_tupleTypeOf ht
              have hslot := h.slots j d slot hd hs
              simp only [DeclSlotOk, hnone2, ht] at hslot
              match slot, hslot with
              | .init rootVal, ⟨hrootWf, hrootVal⟩ =>
                obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hrootWf hres
                obtain ⟨leafVal, hread, hleafValOk, hslice, _hsem⟩ :=
                  resolveFieldPath_read hrootWf hrootVal hres
                cases leafVal with
                | scalar sc =>
                  have hleafValOk' := hleafValOk
                  simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hleafValOk'
                  obtain ⟨hscSz, hscBits⟩ := hleafValOk'
                  have htr : translateTy body.layouts d.ty =
                      some ((TupleSpec.tuple fields size align).toMiniRustTy) := by
                    simp [translateTy, hnone1, hnone2, ht]
                  have hspec := translateFn_local_ty h.hf j d _ hd htr
                  have hplaceBase := evalPlace_local h.shape j hj _ hspec
                  have hL := h.localAllocs_get j d (.init rootVal) hd hs
                  simp only [declSlotData, hnone2, ht] at hL
                  have hdlen : ((TupleSpec.tuple fields size align).encodeVal rootVal).length = size :=
                    TupleSpec.encodeVal_length (.tuple fields size align) rootVal hrootWf
                  have hbound : size < 2 ^ 63 := by
                    simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hrootWf
                    exact hrootWf.1.2
                  have haddr := h.addrs j d hd
                  simp only [AddrOk, hnone2, ht] at haddr
                  obtain ⟨_, haddr0, haddrMax⟩ := haddr
                  have hrootEval : evalPlace m (.Local (localName j)) =
                      .ok (({ ptr := { thin_pointer := fieldPtr ctx j 0, metadata := none },
                               aligned := true },
                             (TupleSpec.tuple fields size align).toMiniRustTy), m) := by
                    simpa using hplaceBase
                  have hpeEval := evalPlace_fieldPath h.shape j (itOf body.layouts d)
                    ((TupleSpec.tuple fields size align).encodeVal rootVal) hL
                    (by rw [hdlen]; exact hbound) haddr0 (by rw [hdlen]; exact haddrMax)
                    (.Local (localName j)) 0 (.tuple fields size align) hrootEval hrootWf
                    (by simp [TupleSpec.size, hdlen]) (.field idx fieldTy :: rest) pe hpe
                    relOff (.scalar leafIt) hres
                  simp only [Nat.zero_add] at hpeEval
                  obtain ⟨m', hm', hshape'⟩ := typedLoad_tuple_slice h.shape j (itOf body.layouts d)
                    ((TupleSpec.tuple fields size align).encodeVal rootVal) hL
                    relOff (.scalar leafIt) (.scalar sc) hleafWf hleafValOk
                    (by rw [hdlen]; exact hrelBound) hslice
                  refine ⟨fun bits hbits => ?_, fun hnone => ?_⟩
                  · simp [opBits, hs, hread] at hbits
                    subst hbits
                    refine ⟨hscBits, m', ?_, ⟨h.hf, hshape', h.nlocals, h.slots, h.addrs, h.declsOk⟩⟩
                    simp only [TupleSpec.toMiniRustTy, TupleSpec.toMiniRustVal] at hpeEval hm' ⊢
                    simp [evalValue, hpeEval, placeLoad, hm']
                  · simp [opBits, hs, hread] at hnone
                | _ => simp [TupleSpec.valOk] at hleafValOk
  | .copy ⟨j, [.index idxLocal]⟩, hok, he =>
    exact evalValue_operand_array_proj h it j (.index idxLocal) (by intro _ _ hc; cases hc) hok e he
  | .copy ⟨j, [.constantIndex offset minLen fromEnd]⟩, hok, he =>
    exact evalValue_operand_array_proj h it j (.constantIndex offset minLen fromEnd)
      (by intro _ _ hc; cases hc) hok e he
  | .constant c, hok, he =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hty, _⟩ := hok
    simp only [operandIntType] at hty
    simp only [translateOperand, hty] at he
    match hv : c.val, he with
    | .scalar (.int ⟨bits, sz⟩), he =>
      simp only at he
      split at he
      · next hc =>
        simp only [Option.some.injEq] at he
        subst he
        obtain ⟨hsz, hb⟩ := hc
        subst hsz
        refine ⟨fun bits' hbits => ?_, fun hnone => by simp [opBits, hv] at hnone⟩
        simp [opBits, hv] at hbits
        subst hbits
        exact ⟨hb, m, by simp [evalValue, evalConstant], h⟩
      · simp at he
  | .copy ⟨j, .downcast _ _ :: rest⟩, hok, he => cases rest <;> simp [operandOk, placeOk, projOk] at hok <;> try split at hok <;> try cases hok <;> try rename_i left right <;> try cases left <;> try simp_all

/-- The bit pattern an Anneal fragment rvalue of type `it` evaluates to, or
`none` when evaluating it is UB. -/
def rvBits (decls : List LocalDecl) (locals : List LocalSlot) (it : Gen.IntType)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Rvalue → Option Nat
  | .use op => opBits locals op
  | .len ⟨j, []⟩ =>
    match decls[j]? with
    | some d =>
      match arrayTypeOf d.ty with
      | some (_, count) => some count
      | none => none
    | none => none
  | .unaryOp uop op => do
    let iuop ← translateUnOp uop
    let x ← opBits locals op
    pure (intUnArith iuop x % 2 ^ (8 * it.size.bytes)).toNat
  | .binaryOp op a b => do
    let iop ← translateBinOp op
    let rhsIt ← operandIntType layouts decls b
    let x ← opBits locals a
    let y ← opBits locals b
    let z ← intBinEval iop (intFromBits x it) (intFromBits y rhsIt) it
    pure (z % 2 ^ (8 * it.size.bytes)).toNat
  | .cast .intToInt op _ => do
    let srcIt ← operandIntType layouts decls op
    let x ← opBits locals op
    pure (intFromBits x srcIt % 2 ^ (8 * it.size.bytes)).toNat
  | _ => none

theorem bringInBounds_eq_intFromBits (it : Gen.IntType) (hgood : GoodSize it.size.bytes) (z : Int) :
    IntType.bring_in_bounds it z = intFromBits (z % 2 ^ (8 * it.size.bytes)).toNat it := by
  have hn : 0 < 8 * it.size.bytes := by have := hgood.pos; omega
  have hn' : 0 < Size.bits it.size := by simpa [Size.bits] using hn
  obtain ⟨hl, hr⟩ := bringInBounds_window z it.signed it.size hn'
  have heq := eq_intFromBits _ it hn (by simpa [Size.bits] using hl) (by simpa [Size.bits] using hr)
  unfold IntType.bring_in_bounds
  rw [heq]
  congr 2
  simpa [Size.bits] using bringInBounds_emod z it.signed it.size

theorem bringInBounds_intUnArith (uop : MirAst.UnOp) (iuop : Gen.IntUnOp)
    (huop : translateUnOp uop = some iuop) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (x : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) :
    IntType.bring_in_bounds it (intUnArith iuop (intFromBits x it)) =
      intFromBits (intUnArith iuop x % 2 ^ (8 * it.size.bytes)).toNat it := by
  rw [bringInBounds_eq_intFromBits it hgood]
  congr 2
  have hpos := two_pow_pos (8 * it.size.bytes)
  have hx' : intFromBits x it % 2 ^ (8 * it.size.bytes) = (x : Int) % 2 ^ (8 * it.size.bytes) := by
    rw [intFromBits_emod x it hx, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hx)]
  exact intUnArith_emod uop iuop huop _ _ _ hx'

/-- Evaluating a translated fragment rvalue. -/
theorem evalValue_rvalue {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals m blk stmt)
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes) (rv : Rvalue)
    (hok : rvalueOk body.layouts body.localDecls it rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    (∀ r, rvBits body.localDecls locals it body.layouts rv = some r →
      r < 2 ^ (8 * it.size.bytes) ∧
      ∃ m', evalValue m e = .ok ((.Int (intFromBits r it), .Int it), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (rvBits body.localDecls locals it body.layouts rv = none →
      ∃ msg, evalValue m e = .error (.ub msg)) := by
  match rv, hok, he with
  | .use op, hok, he =>
    simp only [rvalueOk] at hok
    simp only [translateRvalue] at he
    exact evalValue_operand h it op hok e he
  | .len ⟨j, []⟩, hok, he =>
    simp only [rvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨rfl, _⟩, hok⟩ := hok
    cases hd : body.localDecls[j]? with
    | none => simp [translateRvalue, hd] at he
    | some d =>
      cases ha : arrayTypeOf d.ty with
      | none => simp [translateRvalue, hd, ha] at he
      | some p =>
        obtain ⟨elemIt, count⟩ := p
        simp [translateRvalue, hd, ha] at he
        subst he
        have hdok := h.array_bound j d elemIt count hd ha
        have hpos := (arrayTypeOf_good ha).pos
        have hle : count ≤ count * elemIt.size.bytes := Nat.le_mul_of_pos_right _ hpos
        have hlt : count < 2 ^ (8 * usizeIt.size.bytes) := by
          simp only [usizeIt]; omega
        refine ⟨fun r hr => ?_, fun hnone => by simp [rvBits, hd, ha] at hnone⟩
        simp [rvBits, hd, ha] at hr
        subst hr
        refine ⟨hlt, m, ?_, h⟩
        simp [evalValue, evalConstant, intFromBits, usizeIt]
  | .unaryOp uop op, hok, he =>
    simp only [rvalueOk, Bool.and_eq_true] at hok
    obtain ⟨huop, hok⟩ := hok
    obtain ⟨iuop, hiuop⟩ := Option.isSome_iff_exists.mp huop
    simp only [translateRvalue, hiuop, Option.bind_eq_bind] at he
    cases heo : translateOperand body.localDecls op with
    | none => simp [heo] at he
    | some eo =>
      simp [heo] at he
      subst he
      obtain ⟨haok, hanone⟩ := evalValue_operand h it op hok eo heo
      cases hxo : opBits locals op with
      | none =>
        refine ⟨fun r hr => by simp [rvBits, hiuop, hxo] at hr, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hanone hxo
        exact ⟨msg, by simp [evalValue, hmsg]⟩
      | some x =>
        obtain ⟨hx, m1, hm1, h1⟩ := haok x hxo
        refine ⟨fun r hr => ?_, fun hnone => by simp [rvBits, hiuop, hxo] at hnone⟩
        simp [rvBits, hiuop, hxo] at hr
        subst hr
        have hpos := two_pow_pos (8 * it.size.bytes)
        have hlt : (intUnArith iuop x % 2 ^ (8 * it.size.bytes)).toNat < 2 ^ (8 * it.size.bytes) := by
          have h0 := Int.emod_nonneg (intUnArith iuop x) (Int.ne_of_gt hpos)
          have hlt' := Int.emod_lt_of_pos (intUnArith iuop x) hpos
          have : (((intUnArith iuop x % 2 ^ (8 * it.size.bytes)).toNat : Int)) < 2 ^ (8 * it.size.bytes) := by
            rw [Int.toNat_of_nonneg h0]; exact hlt'
          exact_mod_cast this
        have hrep := canRepresent_intFromBits it _ hgood hlt
        refine ⟨hlt, m1, ?_, h1⟩
        have hbring := bringInBounds_intUnArith uop iuop hiuop it hgood x hx
        have heval := evalIntUnOp_eq uop iuop hiuop (intFromBits x it) it
        cases uop <;> simp [translateUnOp] at hiuop <;> subst hiuop <;>
          simp [evalValue, hm1, evalUnOp, heval, hbring, checkValue, hrep]
  | .binaryOp op a b, hok, he =>
    obtain ⟨iop, rhsIt, hiop, hoka, hrhsTy, hokb, _⟩ := rvalueOk_binaryOp hok
    simp only [translateRvalue, hiop, Option.bind_eq_bind] at he
    cases hea : translateOperand body.localDecls a with
    | none => simp [hea] at he
    | some ea =>
      cases heb : translateOperand body.localDecls b with
      | none => simp [hea, heb] at he
      | some eb =>
        simp [hea, heb] at he
        subst he
        obtain ⟨haok, hanone⟩ := evalValue_operand h it a hoka ea hea
        cases hxa : opBits locals a with
        | none =>
          refine ⟨fun r hr => by simp [rvBits, hiop, hrhsTy, hxa] at hr, fun _ => ?_⟩
          obtain ⟨msg, hmsg⟩ := hanone hxa
          exact ⟨msg, by simp [evalValue, hmsg]⟩
        | some x =>
          obtain ⟨hx, m1, hm1, h1⟩ := haok x hxa
          obtain ⟨hbok, hbnone⟩ := evalValue_operand h1 rhsIt b hokb eb heb
          cases hyb : opBits locals b with
          | none =>
            refine ⟨fun r hr => by simp [rvBits, hiop, hrhsTy, hxa, hyb] at hr, fun _ => ?_⟩
            obtain ⟨msg, hmsg⟩ := hbnone hyb
            exact ⟨msg, by simp [evalValue, hm1, hmsg]⟩
          | some y =>
            obtain ⟨_, m2, hm2, h2⟩ := hbok y hyb
            obtain ⟨hevalOk, hevalNone⟩ :=
              evalIntBinOp_spec op iop hiop (intFromBits x it) (intFromBits y rhsIt) it
            cases hz : intBinEval iop (intFromBits x it) (intFromBits y rhsIt) it with
            | none =>
              refine ⟨fun r hr => by simp [rvBits, hiop, hrhsTy, hxa, hyb, hz] at hr, fun _ => ?_⟩
              obtain ⟨msg, hmsg⟩ := hevalNone hz
              exact ⟨msg, by simp [evalValue, hm1, hm2, evalBinOp, hmsg]⟩
            | some z =>
              refine ⟨fun r hr => ?_, fun hnone => by simp [rvBits, hiop, hrhsTy, hxa, hyb, hz] at hnone⟩
              simp [rvBits, hiop, hrhsTy, hxa, hyb, hz] at hr
              subst hr
              have hpos := two_pow_pos (8 * it.size.bytes)
              refine ⟨?_, m2, ?_, h2⟩
              · have h0 := Int.emod_nonneg z (Int.ne_of_gt hpos)
                have hlt := Int.emod_lt_of_pos z hpos
                have : ((z % 2 ^ (8 * it.size.bytes)).toNat : Int) < 2 ^ (8 * it.size.bytes) := by
                  rw [Int.toNat_of_nonneg h0]; exact hlt
                exact_mod_cast this
              · simp [evalValue, hm1, hm2, evalBinOp, hevalOk z hz,
                  bringInBounds_eq_intFromBits it hgood z]
  | .cast .intToInt op targetTy', hok, he =>
    simp only [rvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨htgt, hsrc⟩ := hok
    cases hsrcIt : operandIntType body.layouts body.localDecls op with
    | none => simp [hsrcIt] at hsrc
    | some srcIt =>
      simp only [hsrcIt] at hsrc
      simp only [translateRvalue, htgt, Option.bind_eq_bind] at he
      cases heo : translateOperand body.localDecls op with
      | none => simp [heo] at he
      | some eo =>
        simp [heo] at he
        subst he
        obtain ⟨haok, hanone⟩ := evalValue_operand h srcIt op hsrc eo heo
        cases hxo : opBits locals op with
        | none =>
          refine ⟨fun r hr => by simp [rvBits, hsrcIt, hxo] at hr, fun _ => ?_⟩
          obtain ⟨msg, hmsg⟩ := hanone hxo
          exact ⟨msg, by simp [evalValue, hmsg]⟩
        | some x =>
          obtain ⟨_, m1, hm1, h1⟩ := haok x hxo
          refine ⟨fun r hr => ?_, fun hnone => by simp [rvBits, hsrcIt, hxo] at hnone⟩
          simp [rvBits, hsrcIt, hxo] at hr
          subst hr
          have hpos := two_pow_pos (8 * it.size.bytes)
          have hlt : (intFromBits x srcIt % 2 ^ (8 * it.size.bytes)).toNat < 2 ^ (8 * it.size.bytes) := by
            have h0 := Int.emod_nonneg (intFromBits x srcIt) (Int.ne_of_gt hpos)
            have hlt' := Int.emod_lt_of_pos (intFromBits x srcIt) hpos
            have : (((intFromBits x srcIt % 2 ^ (8 * it.size.bytes)).toNat : Int)) < 2 ^ (8 * it.size.bytes) := by
              rw [Int.toNat_of_nonneg h0]; exact hlt'
            exact_mod_cast this
          refine ⟨hlt, m1, ?_, h1⟩
          simp [evalValue, hm1, evalUnOp, evalCastOp, bringInBounds_eq_intFromBits it hgood]

/-- The element list an Anneal array-producing rvalue evaluates to, or `none`
when evaluating it is UB. -/
def arrayRvElems (locals : List LocalSlot) (elemIt : Gen.IntType) : Rvalue → Option (List Value)
  | .use (.copy ⟨j, []⟩) =>
    match locals[j]? with
    | some (.init (.aggregate 0 elems)) => some elems
    | _ => none
  | .repeat op count => do
    let b ← opBits locals op
    pure (List.replicate count (.scalar ⟨b, elemIt.size.bytes⟩))
  | .aggregate (.array _) ops =>
    ops.mapM (fun op => do
      let b ← opBits locals op
      pure (.scalar ⟨b, elemIt.size.bytes⟩))
  | _ => none

theorem evalValueList_operands {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (elemIt : Gen.IntType) (ops : List Operand)
    (hok : ops.all (operandOk body.layouts body.localDecls elemIt) = true)
    (es : List Gen.ValueExpr) (hes : ops.mapM (translateOperand body.localDecls) = some es) :
    (∀ elems, (ops.mapM (fun op => do
        let b ← opBits locals op
        pure (Value.scalar ⟨b, elemIt.size.bytes⟩))) = some elems →
      elems.length = ops.length ∧
      (∀ v ∈ elems, ElemOk elemIt v) ∧
      ∃ m', evalValueList m es = .ok (elems.map (valToMiniRust elemIt), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    ((ops.mapM (fun op => do
        let b ← opBits locals op
        pure (Value.scalar ⟨b, elemIt.size.bytes⟩))) = none →
      ∃ msg, evalValueList m es = .error (.ub msg)) := by
  induction ops generalizing m es with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hes
    subst hes
    refine ⟨fun elems hel => ?_, fun hnone => by simp at hnone⟩
    simp at hel
    subst hel
    exact ⟨rfl, by intro v hv; simp at hv, m, rfl, h⟩
  | cons op ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨hok1, hoks⟩ := hok
    simp only [List.mapM_cons, Option.bind_eq_bind] at hes
    cases he1 : translateOperand body.localDecls op with
    | none => simp [he1] at hes
    | some e1 =>
      cases hes' : ops.mapM (translateOperand body.localDecls) with
      | none => simp [he1, hes'] at hes
      | some es' =>
        simp [he1, hes'] at hes
        subst hes
        obtain ⟨haok, hanone⟩ := evalValue_operand h elemIt op hok1 e1 he1
        cases hb1 : opBits locals op with
        | none =>
          refine ⟨fun elems hel => by simp [hb1] at hel, fun _ => ?_⟩
          obtain ⟨msg, hmsg⟩ := hanone hb1
          exact ⟨msg, by simp [evalValueList, hmsg]⟩
        | some b1 =>
          obtain ⟨hb1_lt, m1, hm1, h1⟩ := haok b1 hb1
          obtain ⟨ihok, ihnone⟩ := ih h1 hoks es' hes'
          cases hrest : ops.mapM (fun op => do
              let b ← opBits locals op
              pure (Value.scalar ⟨b, elemIt.size.bytes⟩)) with
          | none =>
            refine ⟨fun elems hel => by rw [List.mapM_cons, hb1, hrest] at hel; simp at hel, fun _ => ?_⟩
            obtain ⟨msg, hmsg⟩ := ihnone hrest
            exact ⟨msg, by simp [evalValueList, hm1, hmsg]⟩
          | some elems' =>
            obtain ⟨hlen', he', m2, hm2, h2⟩ := ihok elems' hrest
            refine ⟨fun elems hel => ?_, fun hnone => by rw [List.mapM_cons, hb1, hrest] at hnone; simp at hnone⟩
            rw [List.mapM_cons, hb1, hrest] at hel
            simp at hel
            subst hel
            refine ⟨by simp [hlen'], ?_, m2, ?_, h2⟩
            · intro v hv
              simp only [List.mem_cons] at hv
              rcases hv with rfl | hv
              · exact ⟨rfl, hb1_lt⟩
              · exact he' v hv
            · simp [evalValueList, hm1, hm2, valToMiniRust]

theorem evalValueList_replicate {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (elemIt : Gen.IntType) (count : Nat) (op : Operand)
    (hok : operandOk body.layouts body.localDecls elemIt op = true)
    (eo : Gen.ValueExpr) (heo : translateOperand body.localDecls op = some eo) :
    (∀ b, opBits locals op = some b →
      b < 2 ^ (8 * elemIt.size.bytes) ∧
      ∃ m', evalValueList m (List.replicate count eo) =
          .ok ((List.replicate count (Value.scalar ⟨b, elemIt.size.bytes⟩)).map (valToMiniRust elemIt), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (0 < count → opBits locals op = none →
      ∃ msg, evalValueList m (List.replicate count eo) = .error (.ub msg)) := by
  induction count generalizing m with
  | zero =>
    obtain ⟨haok, _⟩ := evalValue_operand h elemIt op hok eo heo
    refine ⟨fun b hb => ⟨(haok b hb).1, m, rfl, h⟩, fun hpos => by omega⟩
  | succ k ih =>
    obtain ⟨haok, hanone⟩ := evalValue_operand h elemIt op hok eo heo
    refine ⟨fun b hb => ?_, fun _ hnone => ?_⟩
    · obtain ⟨hb_lt, m1, hm1, h1⟩ := haok b hb
      obtain ⟨_, m2, hm2, h2⟩ := (ih h1).1 b hb
      exact ⟨hb_lt, m2, by simp [List.replicate_succ, evalValueList, hm1, hm2, valToMiniRust], h2⟩
    · obtain ⟨msg, hmsg⟩ := hanone hnone
      exact ⟨msg, by simp [List.replicate_succ, evalValueList, hmsg]⟩

/-- Evaluating a translated array-producing rvalue. -/
theorem evalValue_arrayRvalue {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals m blk stmt)
    (elemIt : Gen.IntType) (count : Nat) (hgood : GoodSize elemIt.size.bytes)
    (rv : Rvalue) (hok : arrayRvalueOk body.layouts body.localDecls elemIt count rv = true)
    (e : Gen.ValueExpr) (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    (∀ elems, arrayRvElems locals elemIt rv = some elems →
      elems.length = count ∧
      (∀ v ∈ elems, ElemOk elemIt v) ∧
      ∃ m', evalValue m e = .ok ((.Tuple (elems.map (valToMiniRust elemIt)), .Array (.Int elemIt) (count : Int)), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (arrayRvElems locals elemIt rv = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  match rv, hok, he with
  | .use (.copy ⟨j, []⟩), hok, he =>
    simp only [arrayRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hj, hty⟩ := hok
    simp only [translateRvalue, translateOperand, translatePlace,
      Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨d, slot, hd, hs⟩ := h.slot_exists j hj
    rw [hd] at hty
    simp only [Option.bind_eq_bind, Option.bind_some] at hty
    have hitd : itOf body.layouts d = elemIt := by simp [itOf, hty]
    have hnone := intTypeOf_none_of_arrayTypeOf hty
    have htr : translateTy body.layouts d.ty = some (.Array (.Int elemIt) (count : Int)) := by
      simp [translateTy, hnone, hty]
    have hspec := translateFn_local_ty h.hf j d _ hd htr
    have hplace := evalPlace_local h.shape j hj _ hspec
    have hL := h.localAllocs_get j d slot hd hs
    rw [hitd] at hL
    simp only [declSlotData, hty] at hL
    have hslot := h.slots j d slot hd hs
    simp only [DeclSlotOk, hty] at hslot
    match slot, hslot, hL with
    | .init (.aggregate 0 elems), ⟨hlen, he⟩, hL =>
      obtain ⟨m1, hm1, hshape1⟩ := typedLoad_array_local h.shape j elemIt count elems
        hgood hlen he hL
      refine ⟨fun elems' hel => ?_, fun hnone => by simp [arrayRvElems, hs] at hnone⟩
      simp [arrayRvElems, hs] at hel
      subst hel
      exact ⟨hlen, he, m1, by simp [evalValue, hplace, placeLoad, hm1],
        ⟨h.hf, hshape1, h.nlocals, h.slots, h.addrs, h.declsOk⟩⟩
  | .aggregate (.array elemTy) ops, hok, he =>
    simp only [arrayRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨heTy, hlenOps⟩, hoks⟩ := hok
    subst hlenOps
    simp only [translateRvalue, heTy, Option.bind_eq_bind, Option.bind_some] at he
    cases hes : ops.mapM (translateOperand body.localDecls) with
    | none => simp [hes] at he
    | some es =>
      simp [hes] at he
      subst he
      obtain ⟨hlok, hlnone⟩ := evalValueList_operands h elemIt ops hoks es hes
      cases hel : ops.mapM (fun op => do
          let b ← opBits locals op
          pure (Value.scalar ⟨b, elemIt.size.bytes⟩)) with
      | none =>
        refine ⟨(fun elems h1 => by rw [arrayRvElems, hel] at h1; contradiction), fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hlnone hel
        exact ⟨msg, by simp [evalValue, hmsg]⟩
      | some elems =>
        obtain ⟨hlen, he, m1, hm1, h1⟩ := hlok elems hel
        refine ⟨fun elems' h2 => ?_, (fun hnone => by rw [arrayRvElems, hel] at hnone; contradiction)⟩
        rw [arrayRvElems, hel] at h2
        cases h2
        refine ⟨hlen, he, m1, ?_, h1⟩
        simp [evalValue, hm1]
  | .repeat op n, hok, he =>
    simp only [arrayRvalueOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨rfl, hcnt⟩, hokOp⟩ := hok
    have hopTy := operandIntType_of_operandOk hokOp
    simp only [translateRvalue, hopTy, Option.bind_eq_bind, Option.bind_some] at he
    cases heo : translateOperand body.localDecls op with
    | none => simp [heo] at he
    | some eo =>
      simp [heo] at he
      subst he
      obtain ⟨hrepOk, hrepNone⟩ := evalValueList_replicate h elemIt n op hokOp eo heo
      cases hb : opBits locals op with
      | none =>
        refine ⟨fun elems hel => by simp [arrayRvElems, hb] at hel, fun _ => ?_⟩
        rcases hcnt with hposCnt | hconst
        · obtain ⟨msg, hmsg⟩ := hrepNone hposCnt hb
          exact ⟨msg, by simp [evalValue, hmsg]⟩
        · cases op with
          | copy _ => simp at hconst
          | move _ => simp at hconst
          | constant c =>
            simp only [translateOperand] at heo
            match hv : c.val, heo with
            | .scalar (.int sc), heo => simp [opBits, hv] at hb
      | some b =>
        obtain ⟨hb_lt, m1, hm1, h1⟩ := hrepOk b hb
        refine ⟨fun elems hel => ?_, fun hnone => by simp [arrayRvElems, hb] at hnone⟩
        simp [arrayRvElems, hb] at hel
        subst hel
        have hlen : (List.replicate n (Value.scalar ⟨b, elemIt.size.bytes⟩)).length = n := by simp
        have he : ∀ v ∈ List.replicate n (Value.scalar ⟨b, elemIt.size.bytes⟩), ElemOk elemIt v := by
          intro v hv
          rw [List.eq_of_mem_replicate hv]
          exact ⟨rfl, hb_lt⟩
        refine ⟨hlen, he, m1, ?_, h1⟩
        simp [evalValue, hm1]

/-- Value an operand `op` of `TupleSpec` `spec` evaluates to in Anneal, or `none`
when evaluating it is UB. -/
def specOpVal (locals : List LocalSlot) (spec : TupleSpec) (op : Operand) : Option Value :=
  match spec with
  | .scalar it => do
    let b ← opBits locals op
    pure (.scalar ⟨b, it.size.bytes⟩)
  | .tuple _ _ _ =>
    match op with
    | .copy ⟨j, projs⟩ =>
      match locals[j]? with
      | some (.init rootVal) => readFieldPath rootVal projs
      | _ => none
    | _ => none

/-- Pointwise evaluation of aggregate field operands against `fields`. -/
def tupleFieldsOpsVal (locals : List LocalSlot) :
    List (Nat × TupleSpec) → List Operand → Option (List Value)
  | [], [] => some []
  | (_, fSpec) :: restF, op :: restOps => do
    let v ← specOpVal locals fSpec op
    let vs ← tupleFieldsOpsVal locals restF restOps
    pure (v :: vs)
  | _, _ => none

/-- Value a tuple/struct-producing rvalue evaluates to in Anneal, or `none`
when evaluating it is UB. -/
def tupleRvVal (locals : List LocalSlot) (fields : List (Nat × TupleSpec)) :
    Rvalue → Option Value
  | .use (.copy ⟨j, projs⟩) =>
    match locals[j]? with
    | some (.init rootVal) => readFieldPath rootVal projs
    | _ => none
  | .aggregate .tuple ops => do
    let vals ← tupleFieldsOpsVal locals fields ops
    pure (.aggregate 0 vals)
  | .aggregate (.adt _ 0 none) ops => do
    let vals ← tupleFieldsOpsVal locals fields ops
    pure (.aggregate 0 vals)
  | _ => none

theorem tuplePlaceSpec_resolve {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {p : MirAst.Place} {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tuplePlaceSpec layouts decls p = some (fields, size, align)) :
    ∃ d rootFields rootSize rootAlign relOff,
      p.local_ < decls.length ∧
      decls[p.local_]? = some d ∧
      tupleTypeOf layouts d.ty = some (rootFields, rootSize, rootAlign) ∧
      resolveFieldPath layouts (.tuple rootFields rootSize rootAlign) p.projection =
        some (relOff, .tuple fields size align) ∧
      translatePlace decls p = translateFieldPlace (.Local (localName p.local_)) p.projection := by
  match p, h with
  | ⟨j, []⟩, h =>
    simp only [tuplePlaceSpec] at h
    split at h
    · next hj =>
      cases hd : decls[j]? with
      | none => simp [hd] at h
      | some d =>
        simp only [hd, Option.bind_eq_bind, Option.bind_some] at h
        exact ⟨d, fields, size, align, 0, hj, rfl, h, rfl, rfl⟩
    · simp at h
  | ⟨j, .field idx fieldTy :: rest⟩, h =>
    simp only [tuplePlaceSpec] at h
    split at h
    · next hj =>
      cases hd : decls[j]? with
      | none => simp [hd] at h
      | some d =>
        simp only [hd, Option.bind_eq_bind, Option.bind_some] at h
        cases ht : tupleTypeOf layouts d.ty with
        | none => simp [ht] at h
        | some rpair =>
          obtain ⟨rootFields, rootSize, rootAlign⟩ := rpair
          simp only [ht, Option.bind_some] at h
          cases hres : resolveFieldPath layouts (.tuple rootFields rootSize rootAlign)
              (.field idx fieldTy :: rest) with
          | none => simp [hres] at h
          | some lpair =>
            obtain ⟨relOff, leafSpec⟩ := lpair
            simp only [hres, Option.bind_some] at h
            cases leafSpec with
            | scalar _ => simp at h
            | tuple subFields subSize subAlign =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl, rfl⟩
              exact ⟨d, rootFields, rootSize, rootAlign, relOff, hj, rfl, ht, hres, rfl⟩
    · simp at h

theorem evalPlace_tuplePlace {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (p : MirAst.Place) (fields : List (Nat × TupleSpec)) (size align : Nat)
    (htp : tuplePlaceSpec body.layouts body.localDecls p = some (fields, size, align))
    (pe : Gen.PlaceExpr) (hpe : translatePlace body.localDecls p = some pe) :
    ∃ d rootFields rootSize rootAlign rootVal relOff,
      p.local_ < body.localDecls.length ∧
      body.localDecls[p.local_]? = some d ∧
      tupleTypeOf body.layouts d.ty = some (rootFields, rootSize, rootAlign) ∧
      locals[p.local_]? = some (.init rootVal) ∧
      (TupleSpec.tuple rootFields rootSize rootAlign).wf = true ∧
      (TupleSpec.tuple rootFields rootSize rootAlign).valOk rootVal = true ∧
      resolveFieldPath body.layouts (.tuple rootFields rootSize rootAlign) p.projection =
        some (relOff, .tuple fields size align) ∧
      (TupleSpec.tuple fields size align).wf = true ∧
      relOff + size ≤ rootSize ∧
      evalPlace m pe =
        .ok (({ ptr := { thin_pointer := fieldPtr ctx p.local_ relOff, metadata := none },
                 aligned := true },
               (TupleSpec.tuple fields size align).toMiniRustTy), m) := by
  obtain ⟨d, rootFields, rootSize, rootAlign, relOff, hj, hd, ht, hres, htrPlace⟩ :=
    tuplePlaceSpec_resolve htp
  rw [htrPlace] at hpe
  obtain ⟨_, slot, hd', hs⟩ := h.slot_exists p.local_ hj
  rw [hd] at hd'; cases hd'
  have hnone1 := intTypeOf_none_of_tupleTypeOf ht
  have hnone2 := arrayTypeOf_none_of_tupleTypeOf ht
  have hslot := h.slots p.local_ d slot hd hs
  simp only [DeclSlotOk, hnone2, ht] at hslot
  match slot, hslot with
  | .init rootVal, ⟨hrootWf, hrootVal⟩ =>
    obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hrootWf hres
    have htr : translateTy body.layouts d.ty =
        some ((TupleSpec.tuple rootFields rootSize rootAlign).toMiniRustTy) := by
      simp [translateTy, hnone1, hnone2, ht]
    have hspec := translateFn_local_ty h.hf p.local_ d _ hd htr
    have hplaceBase := evalPlace_local h.shape p.local_ hj _ hspec
    have hL := h.localAllocs_get p.local_ d (.init rootVal) hd hs
    simp only [declSlotData, hnone2, ht] at hL
    have hdlen : ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal).length = rootSize :=
      TupleSpec.encodeVal_length (.tuple rootFields rootSize rootAlign) rootVal hrootWf
    have hbound : rootSize < 2 ^ 63 := by
      simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hrootWf
      exact hrootWf.1.2
    have haddr := h.addrs p.local_ d hd
    simp only [AddrOk, hnone2, ht] at haddr
    obtain ⟨_, haddr0, haddrMax⟩ := haddr
    have hrootEval : evalPlace m (.Local (localName p.local_)) =
        .ok (({ ptr := { thin_pointer := fieldPtr ctx p.local_ 0, metadata := none },
                 aligned := true },
               (TupleSpec.tuple rootFields rootSize rootAlign).toMiniRustTy), m) := by
      simpa using hplaceBase
    have hpeEval := evalPlace_fieldPath h.shape p.local_ (itOf body.layouts d)
      ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal) hL
      (by rw [hdlen]; exact hbound) haddr0 (by rw [hdlen]; exact haddrMax)
      (.Local (localName p.local_)) 0 (.tuple rootFields rootSize rootAlign) hrootEval hrootWf
      (by simp [TupleSpec.size, hdlen]) p.projection pe hpe
      relOff (.tuple fields size align) hres
    simp only [Nat.zero_add] at hpeEval
    exact ⟨d, rootFields, rootSize, rootAlign, rootVal, relOff,
      hj, hd, ht, hs, hrootWf, hrootVal, hres, hleafWf, hrelBound, hpeEval⟩

theorem evalValue_specOperand {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (spec : TupleSpec) (op : Operand)
    (hok : specOperandOk body.layouts body.localDecls spec op = true)
    (e : Gen.ValueExpr) (he : translateOperand body.localDecls op = some e) :
    (∀ v, specOpVal locals spec op = some v →
      spec.valOk v = true ∧
      ∃ m', evalValue m e = .ok ((spec.toMiniRustVal v, spec.toMiniRustTy), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (specOpVal locals spec op = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  cases spec with
  | scalar it =>
    simp only [specOperandOk] at hok
    obtain ⟨haok, hanone⟩ := evalValue_operand h it op hok e he
    cases hb : opBits locals op with
    | none =>
      refine ⟨fun v hv => by simp [specOpVal, hb] at hv, fun _ => hanone hb⟩
    | some b =>
      obtain ⟨hb_lt, m1, hm1, h1⟩ := haok b hb
      refine ⟨fun v hv => ?_, fun hnone => by simp [specOpVal, hb] at hnone⟩
      simp [specOpVal, hb] at hv
      subst hv
      exact ⟨by simp [TupleSpec.valOk, hb_lt], m1, hm1, h1⟩
  | tuple fields size align =>
    cases op with
    | move _ | constant _ => simp [specOperandOk] at hok
    | copy p =>
      simp only [specOperandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨htp, _⟩ := hok
      simp only [translateOperand] at he
      cases hpe : translatePlace body.localDecls p with
      | none => simp [hpe] at he
      | some pe =>
        simp only [hpe, Option.map_some, Option.some.injEq] at he
        subst he
        obtain ⟨d, rootFields, rootSize, rootAlign, rootVal, relOff,
          _, hd, ht, hs, hrootWf, hrootVal, hres, hleafWf, hrelBound, hpeEval⟩ :=
          evalPlace_tuplePlace h p fields size align htp pe hpe
        obtain ⟨leafVal, hread, hleafValOk, hslice, _⟩ :=
          resolveFieldPath_read hrootWf hrootVal hres
        have hnone2 := arrayTypeOf_none_of_tupleTypeOf ht
        have hL := h.localAllocs_get p.local_ d (.init rootVal) hd hs
        simp only [declSlotData, hnone2, ht] at hL
        have hdlen : ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal).length = rootSize :=
          TupleSpec.encodeVal_length (.tuple rootFields rootSize rootAlign) rootVal hrootWf
        obtain ⟨m', hm', hshape'⟩ := typedLoad_tuple_slice h.shape p.local_ (itOf body.layouts d)
          ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal) hL
          relOff (.tuple fields size align) leafVal hleafWf hleafValOk
          (by rw [hdlen]; exact hrelBound) hslice
        refine ⟨fun v hv => ?_, fun hnone => ?_⟩
        · cases p; simp [specOpVal, hs, hread] at hv
          subst hv
          exact ⟨hleafValOk, m', by simp [evalValue, hpeEval, placeLoad, hm'],
            ⟨h.hf, hshape', h.nlocals, h.slots, h.addrs, h.declsOk⟩⟩
        · cases p; simp [specOpVal, hs, hread] at hnone

theorem evalValueList_tupleFields {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (fields : List (Nat × TupleSpec)) (ops : List Operand)
    (hok : tupleFieldsOperandOk body.layouts body.localDecls fields ops = true)
    (es : List Gen.ValueExpr) (hes : ops.mapM (translateOperand body.localDecls) = some es) :
    (∀ vals, tupleFieldsOpsVal locals fields ops = some vals →
      TupleSpec.fieldsValOk fields vals = true ∧
      ∃ m', evalValueList m es = .ok (TupleSpec.fieldsToMiniRustVal fields vals, m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (tupleFieldsOpsVal locals fields ops = none →
      ∃ msg, evalValueList m es = .error (.ub msg)) := by
  induction fields generalizing ops m es with
  | nil =>
    cases ops <;> simp [tupleFieldsOperandOk] at hok
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hes
    subst hes
    refine ⟨fun vals hvals => ?_, fun hnone => by simp [tupleFieldsOpsVal] at hnone⟩
    simp [tupleFieldsOpsVal] at hvals
    subst hvals
    exact ⟨rfl, m, rfl, h⟩
  | cons f restF ih =>
    obtain ⟨off, fSpec⟩ := f
    cases ops with
    | nil => simp [tupleFieldsOperandOk] at hok
    | cons op restOps =>
      simp only [tupleFieldsOperandOk, Bool.and_eq_true] at hok
      obtain ⟨hok1, hoks⟩ := hok
      simp only [List.mapM_cons, Option.bind_eq_bind] at hes
      cases he1 : translateOperand body.localDecls op with
      | none => simp [he1] at hes
      | some e1 =>
        cases hes' : restOps.mapM (translateOperand body.localDecls) with
        | none => simp [he1, hes'] at hes
        | some es' =>
          simp [he1, hes'] at hes
          subst hes
          obtain ⟨haok, hanone⟩ := evalValue_specOperand h fSpec op hok1 e1 he1
          cases hv1 : specOpVal locals fSpec op with
          | none =>
            refine ⟨fun vals hvals => by simp [tupleFieldsOpsVal, hv1] at hvals, fun _ => ?_⟩
            obtain ⟨msg, hmsg⟩ := hanone hv1
            exact ⟨msg, by simp [evalValueList, hmsg]⟩
          | some v1 =>
            obtain ⟨hv1Ok, m1, hm1, h1⟩ := haok v1 hv1
            obtain ⟨ihok, ihnone⟩ := ih h1 restOps hoks es' hes'
            cases hrest : tupleFieldsOpsVal locals restF restOps with
            | none =>
              refine ⟨fun vals hvals => by simp [tupleFieldsOpsVal, hv1, hrest] at hvals, fun _ => ?_⟩
              obtain ⟨msg, hmsg⟩ := ihnone hrest
              exact ⟨msg, by simp [evalValueList, hm1, hmsg]⟩
            | some vals' =>
              obtain ⟨hvals'Ok, m2, hm2, h2⟩ := ihok vals' hrest
              refine ⟨fun vals hvals => ?_, fun hnone => by simp [tupleFieldsOpsVal, hv1, hrest] at hnone⟩
              simp [tupleFieldsOpsVal, hv1, hrest] at hvals
              subst hvals
              exact ⟨by simp [TupleSpec.fieldsValOk, hv1Ok, hvals'Ok], m2,
                by simp [evalValueList, hm1, hm2, TupleSpec.fieldsToMiniRustVal], h2⟩

theorem evalValue_tupleRvalue {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (dstTy : MirAst.Ty) (fields : List (Nat × TupleSpec)) (size align : Nat)
    (rv : Rvalue) (hok : tupleRvalueOk body.layouts body.localDecls dstTy fields size align rv = true)
    (e : Gen.ValueExpr) (he : translateRvalue body.layouts body.localDecls (some dstTy) rv = some e) :
    (∀ val, tupleRvVal locals fields rv = some val →
      (TupleSpec.tuple fields size align).valOk val = true ∧
      ∃ m', evalValue m e = .ok (((TupleSpec.tuple fields size align).toMiniRustVal val,
                                    (TupleSpec.tuple fields size align).toMiniRustTy), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (tupleRvVal locals fields rv = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  match rv, hok, he with
  | .use (.copy p), hok, he =>
    simp only [tupleRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨htp, hpeSome⟩ := hok
    simp only [translateRvalue] at he
    have hspecOk : specOperandOk body.layouts body.localDecls (.tuple fields size align) (.copy p) = true := by
      simp [specOperandOk, htp, translateOperand, hpeSome]
    have hev := evalValue_specOperand h (.tuple fields size align) (.copy p) hspecOk e he
    cases p; simpa [tupleRvVal, specOpVal] using hev
  | .aggregate .tuple ops, hok, he | .aggregate (.adt _ 0 none) ops, hok, he =>
    simp only [tupleRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨_, htup⟩, hfieldsOk⟩ := hok
    simp only [translateRvalue, htup, Option.bind_eq_bind, Option.bind_some] at he
    cases hes : ops.mapM (translateOperand body.localDecls) with
    | none => simp [hes] at he
    | some es =>
      simp [hes] at he
      subst he
      obtain ⟨hlok, hlnone⟩ := evalValueList_tupleFields h fields ops hfieldsOk es hes
      cases hvals : tupleFieldsOpsVal locals fields ops with
      | none =>
        refine ⟨fun val hval => by simp [tupleRvVal, hvals] at hval, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hlnone hvals
        exact ⟨msg, by simp [evalValue, hmsg]⟩
      | some vals =>
        obtain ⟨hvalsOk, m1, hm1, h1⟩ := hlok vals hvals
        refine ⟨fun val hval => ?_, fun hnone => by simp [tupleRvVal, hvals] at hnone⟩
        simp [tupleRvVal, hvals] at hval
        subst hval
        exact ⟨by simp [TupleSpec.valOk, TupleSpec.fieldsValOk_length hvalsOk, hvalsOk],
          m1, by simp [evalValue, hm1, TupleSpec.toMiniRustVal], h1⟩

/-! ## Frames and control flow -/

theorem mutateCurFrame_eq {m : Mach} {ctx : Ctx} {fr : Frame} {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, fr] allocs) (g : Frame → Frame) :
    ∃ m', mutateCurFrame m g = .ok m' ∧ Shape m' ctx [ctx.caller, g fr] allocs := by
  refine ⟨{ m with threads := [thread1 ctx [ctx.caller, g fr]] }, ?_, ⟨rfl, h.active, h.allocs⟩⟩
  simp [mutateCurFrame, activeThread, listIndex, h.threads, h.active, thread1, listSet]

theorem jumpToBlock_callee {m : Mach} {ctx : Ctx} {f : Gen.Function} {n blk stmt : Nat}
    {allocs : List Gen.Allocation} (h : Shape m ctx [ctx.caller, calleeFrame f ctx n blk stmt] allocs)
    (t : Nat) :
    ∃ m', jumpToBlock m (bbName t) = .ok m' ∧ Shape m' ctx [ctx.caller, calleeFrame f ctx n t 0] allocs :=
  mutateCurFrame_eq h _

theorem bumpStmt_callee {m : Mach} {ctx : Ctx} {f : Gen.Function} {n blk stmt : Nat}
    {allocs : List Gen.Allocation} (h : Shape m ctx [ctx.caller, calleeFrame f ctx n blk stmt] allocs) :
    ∃ m', mutateCurFrame m (fun fr => { fr with next_stmt := fr.next_stmt + 1 }) = .ok m' ∧
      Shape m' ctx [ctx.caller, calleeFrame f ctx n blk (stmt + 1)] allocs := by
  obtain ⟨m', hm', hs⟩ := mutateCurFrame_eq h (fun fr => { fr with next_stmt := fr.next_stmt + 1 })
  refine ⟨m', hm', ?_⟩
  have : ({ calleeFrame f ctx n blk stmt with
      next_stmt := (calleeFrame f ctx n blk stmt).next_stmt + 1 } : Frame) =
      calleeFrame f ctx n blk (stmt + 1) := by
    simp [calleeFrame]
  rw [this] at hs; exact hs

/-- `Machine::eval_statement` on a translated fragment scalar assignment. -/
theorem evalStatement_assign {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (hit : intTypeOf d.ty = some (itOf body.layouts d)) (rv : Rvalue)
    (hok : rvalueOk body.layouts body.localDecls (itOf body.layouts d) rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    (∀ r, rvBits body.localDecls locals (itOf body.layouts d) body.layouts rv = some r →
      ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
        FrameOk body f ctx (locals.set i (.init (.scalar ⟨r, (itOf body.layouts d).size.bytes⟩))) m' blk stmt) ∧
    (rvBits body.localDecls locals (itOf body.layouts d) body.layouts rv = none →
      ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood := h.decl_good i d hd
  have harrNone := arrayTypeOf_none_of_intTypeOf hit
  have htupNone := tupleTypeOf_none_of_intTypeOf (layouts := body.layouts) hit
  have htr : translateTy body.layouts d.ty = some (.Int (itOf body.layouts d)) := by
    simp [translateTy, hit]
  have hspec := translateFn_local_ty h.hf i d _ hd htr
  have hplace := evalPlace_local h.shape i hi _ hspec
  obtain ⟨hrok, hrnone⟩ := evalValue_rvalue h (itOf body.layouts d) hgood rv hok e he
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  refine ⟨fun r hr => ?_, fun hnone => ?_⟩
  · obtain ⟨hrlt, m1, hm1, h1⟩ := hrok r hr
    have hL1 := h1.localAllocs_get i d slot hd hs
    simp only [declSlotData, harrNone, htupNone] at hL1
    have hrep := canRepresent_intFromBits (itOf body.layouts d) r hgood hrlt
    have hst := typedStore_local h1.shape i (itOf body.layouts d) _ (intFromBits r (itOf body.layouts d)) hgood hL1
      (slotData_length _ _) hrep ⟨1⟩ (isAligned_one _)
    have hres : (intFromBits r (itOf body.layouts d) % 2 ^ (8 * (itOf body.layouts d).size.bytes)).toNat = r := by
      rw [intFromBits_emod r _ hrlt]; simp
    rw [hres] at hst
    have hset := localAllocsFrom_set body.layouts ctx 0 body.localDecls locals i d
      (.init (.scalar ⟨r, (itOf body.layouts d).size.bytes⟩)) hd
    simp only [Nat.zero_add, declSlotData, harrNone, htupNone, slotData] at hset
    refine ⟨withMem m1 (ctx.base ++ localAllocs body.layouts ctx body.localDecls
        (locals.set i (.init (.scalar ⟨r, (itOf body.layouts d).size.bytes⟩))))
        ⟨.Store, .None, ctx.addrs.getD i 0, (itOf body.layouts d).size⟩, ?_, ?_⟩
    · have hst' := hst
      simp only [localAllocs] at hst'
      rw [hset] at hst'
      simp [evalStatement, hplace, hm1, placeStore, hst', localAllocs]
    refine ⟨h.hf, withMem_shape h1.shape _, by simp [h.nlocals], ?_, h.addrs, h.declsOk⟩
    · intro j d' slot' hd' hs'
      by_cases hij : i = j
      · subst hij
        rw [hd] at hd'; cases hd'
        simp [List.getElem?_set_self (by rw [h.nlocals]; exact hi)] at hs'
        subst hs'
        simp [DeclSlotOk, harrNone, htupNone, SlotOk, hrlt]
      · rw [List.getElem?_set_ne hij] at hs'
        exact h.slots j d' slot' hd' hs'
  · obtain ⟨msg, hmsg⟩ := hrnone hnone
    exact ⟨msg, by simp [evalStatement, hplace, hmsg]⟩

/-- `Machine::eval_statement` on a translated fragment array assignment. -/
theorem evalStatement_assign_array {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (elemIt : Gen.IntType) (count : Nat) (ha : arrayTypeOf d.ty = some (elemIt, count))
    (rv : Rvalue) (hok : arrayRvalueOk body.layouts body.localDecls elemIt count rv = true)
    (e : Gen.ValueExpr) (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    (∀ elems, arrayRvElems locals elemIt rv = some elems →
      ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
        FrameOk body f ctx (locals.set i (.init (.aggregate 0 elems))) m' blk stmt) ∧
    (arrayRvElems locals elemIt rv = none →
      ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood := arrayTypeOf_good ha
  have hnone := intTypeOf_none_of_arrayTypeOf ha
  have htr : translateTy body.layouts d.ty = some (.Array (.Int elemIt) (count : Int)) := by
    simp [translateTy, hnone, ha]
  have hspec := translateFn_local_ty h.hf i d _ hd htr
  have hplace := evalPlace_local h.shape i hi _ hspec
  obtain ⟨hrok, hrnone⟩ := evalValue_arrayRvalue h elemIt count hgood rv hok e he
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  have hslot := h.slots i d slot hd hs
  have hdlen := declSlotData_length d slot hslot
  simp only [ha] at hdlen
  have hitd : itOf body.layouts d = elemIt := by simp [itOf, ha]
  refine ⟨fun elems hr => ?_, fun hnone => ?_⟩
  · obtain ⟨hlen, helemOk, m1, hm1, h1⟩ := hrok elems hr
    have hL1 := h1.localAllocs_get i d slot hd hs
    rw [hitd] at hL1
    have hst := typedStore_array_local h1.shape i elemIt count _ elems hgood hL1
      hdlen hlen helemOk
    have hset := localAllocsFrom_set body.layouts ctx 0 body.localDecls locals i d
      (.init (.aggregate 0 elems)) hd
    simp only [Nat.zero_add, hitd, declSlotData, ha] at hset
    refine ⟨withMem m1 (ctx.base ++ localAllocs body.layouts ctx body.localDecls
        (locals.set i (.init (.aggregate 0 elems))))
        ⟨.Store, .None, ctx.addrs.getD i 0, ⟨count * elemIt.size.bytes⟩⟩, ?_, ?_⟩
    · have hst' := hst
      simp only [localAllocs] at hst'
      rw [hset] at hst'
      simp [evalStatement, hplace, hm1, placeStore, hst', localAllocs]
    refine ⟨h.hf, withMem_shape h1.shape _, by simp [h.nlocals], ?_, h.addrs, h.declsOk⟩
    · intro j d' slot' hd' hs'
      by_cases hij : i = j
      · subst hij
        rw [hd] at hd'; cases hd'
        simp [List.getElem?_set_self (by rw [h.nlocals]; exact hi)] at hs'
        subst hs'
        simp [DeclSlotOk, ha, hlen]
        exact helemOk
      · rw [List.getElem?_set_ne hij] at hs'
        exact h.slots j d' slot' hd' hs'
  · obtain ⟨msg, hmsg⟩ := hrnone hnone
    exact ⟨msg, by simp [evalStatement, hplace, hmsg]⟩

/-- `Machine::eval_statement` on a translated fragment indexed array assignment `arr[proj] = rv`. -/
theorem evalStatement_assign_index {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (elemIt : Gen.IntType) (count : Nat) (ha : arrayTypeOf d.ty = some (elemIt, count))
    (proj : ProjectionElem) (hproj : projOk body.localDecls count proj = true)
    (pe : Gen.PlaceExpr) (hpe : translatePlace body.localDecls ⟨i, [proj]⟩ = some pe)
    (rv : Rvalue) (hok : rvalueOk body.layouts body.localDecls elemIt rv = true)
    (e : Gen.ValueExpr) (he : translateRvalue body.layouts body.localDecls targetTy rv = some e)
    (elems : List Value) (hs : locals[i]? = some (.init (.aggregate 0 elems))) :
    (∀ idx r, projIdx locals count proj = some idx →
      rvBits body.localDecls locals elemIt body.layouts rv = some r →
      ∃ m', evalStatement m (.Assign pe e) = .ok m' ∧
        FrameOk body f ctx
          (locals.set i (.init (.aggregate 0 (elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩)))))
          m' blk stmt) ∧
    (projIdx locals count proj = none ∨ rvBits body.localDecls locals elemIt body.layouts rv = none →
      ∃ msg, evalStatement m (.Assign pe e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood := arrayTypeOf_good ha
  obtain ⟨hpok, hpnone⟩ := evalPlace_proj h i d hd elemIt count ha proj hproj pe hpe
  have hslot := h.slots i d (.init (.aggregate 0 elems)) hd hs
  simp only [DeclSlotOk, ha] at hslot
  obtain ⟨hlen, helemOk⟩ := hslot
  have hitd : itOf body.layouts d = elemIt := by simp [itOf, ha]
  refine ⟨fun idx r hidx hr => ?_, fun hnone => ?_⟩
  · obtain ⟨hidx_lt, m1, hm1, h1⟩ := hpok idx hidx
    obtain ⟨hrok, _⟩ := evalValue_rvalue h1 elemIt hgood rv hok e he
    obtain ⟨hrlt, m2, hm2, h2⟩ := hrok r hr
    have hL2 := h2.localAllocs_get i d (.init (.aggregate 0 elems)) hd hs
    rw [hitd] at hL2
    simp only [declSlotData, ha] at hL2
    have hst := typedStore_array_elem h2.shape i idx elemIt count elems r hgood hlen hidx_lt hrlt hL2
    have hset := localAllocsFrom_set body.layouts ctx 0 body.localDecls locals i d
      (.init (.aggregate 0 (elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩)))) hd
    simp only [Nat.zero_add, hitd, declSlotData, ha] at hset
    refine ⟨withMem m2 (ctx.base ++ localAllocs body.layouts ctx body.localDecls
        (locals.set i (.init (.aggregate 0 (elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩))))))
        ⟨.Store, .None, (elemPtr ctx i idx elemIt).addr, elemIt.size⟩, ?_, ?_⟩
    · have hst' := hst
      simp only [localAllocs] at hst'
      rw [hset] at hst'
      simp [evalStatement, hm1, hm2, placeStore, hst', localAllocs]
    refine ⟨h.hf, withMem_shape h2.shape _, by simp [h.nlocals], ?_, h.addrs, h.declsOk⟩
    · intro j d' slot' hd' hs'
      by_cases hij : i = j
      · subst hij
        rw [hd] at hd'; cases hd'
        simp [List.getElem?_set_self (by rw [h.nlocals]; exact hi)] at hs'
        subst hs'
        simp only [DeclSlotOk, ha, List.length_set, hlen, true_and]
        intro v hv
        rcases List.mem_or_eq_of_mem_set hv with hv' | rfl
        · exact helemOk v hv'
        · exact ⟨rfl, hrlt⟩
      · rw [List.getElem?_set_ne hij] at hs'
        exact h.slots j d' slot' hd' hs'
  · cases hidx : projIdx locals count proj with
    | none =>
      obtain ⟨msg, hmsg⟩ := hpnone hidx
      exact ⟨msg, by simp [evalStatement, hmsg]⟩
    | some idx =>
      rcases hnone with hidxNone | hrNone
      · rw [hidx] at hidxNone; cases hidxNone
      · obtain ⟨_, m1, hm1, h1⟩ := hpok idx hidx
        obtain ⟨_, hrnone⟩ := evalValue_rvalue h1 elemIt hgood rv hok e he
        obtain ⟨msg, hmsg⟩ := hrnone hrNone
        exact ⟨msg, by simp [evalStatement, hm1, hmsg]⟩

/-- `Machine::eval_statement` on a translated fragment tuple/struct assignment
(either whole-local `_i = rv` or nested tuple/struct field `_i.f1...fk = rv`). -/
theorem evalStatement_assign_tuple {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals m blk stmt)
    (dst : MirAst.Place) (dstTy : MirAst.Ty)
    (fields : List (Nat × TupleSpec)) (size align : Nat)
    (htp : tuplePlaceSpec body.layouts body.localDecls dst = some (fields, size, align))
    (pe : Gen.PlaceExpr) (hpe : translatePlace body.localDecls dst = some pe)
    (rv : Rvalue) (hok : tupleRvalueOk body.layouts body.localDecls dstTy fields size align rv = true)
    (e : Gen.ValueExpr) (he : translateRvalue body.layouts body.localDecls (some dstTy) rv = some e)
    (rootVal : Value) (hs : locals[dst.local_]? = some (.init rootVal)) :
    (∀ newVal, tupleRvVal locals fields rv = some newVal →
      ∃ newRootVal m',
        writeFieldPath rootVal dst.projection newVal = some newRootVal ∧
        (∀ locals', MirSemantics.writeProjectedValue locals' rootVal dst.projection newVal = .ok newRootVal) ∧
        evalStatement m (.Assign pe e) = .ok m' ∧
        FrameOk body f ctx (locals.set dst.local_ (.init newRootVal)) m' blk stmt) ∧
    (tupleRvVal locals fields rv = none →
      ∃ msg, evalStatement m (.Assign pe e) = .error (.ub msg)) := by
  obtain ⟨d, rootFields, rootSize, rootAlign, rootVal', relOff,
    hj, hd, ht, hs', hrootWf, hrootVal, hres, hleafWf, hrelBound, hpeEval⟩ :=
    evalPlace_tuplePlace h dst fields size align htp pe hpe
  rw [hs] at hs'; cases hs'
  obtain ⟨hrok, hrnone⟩ := evalValue_tupleRvalue h dstTy fields size align rv hok e he
  have hnone2 := arrayTypeOf_none_of_tupleTypeOf ht
  have hdlen : ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal).length = rootSize :=
    TupleSpec.encodeVal_length (.tuple rootFields rootSize rootAlign) rootVal hrootWf
  refine ⟨fun newVal hr => ?_, fun hnone => ?_⟩
  · obtain ⟨hnewValOk, m1, hm1, h1⟩ := hrok newVal hr
    obtain ⟨newRootVal, hwpath, hnewRootOk, hnewEnc, hwsem⟩ :=
      resolveFieldPath_write hrootWf hrootVal hres hnewValOk
    have hL1 := h1.localAllocs_get dst.local_ d (.init rootVal) hd hs
    simp only [declSlotData, hnone2, ht] at hL1
    have hst := typedStore_tuple_slice h1.shape dst.local_ (itOf body.layouts d)
      ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal) hL1
      relOff (.tuple fields size align) newVal hleafWf hnewValOk
      (by rw [hdlen]; exact hrelBound)
    rw [← hnewEnc] at hst
    have hset := localAllocsFrom_set body.layouts ctx 0 body.localDecls locals dst.local_ d
      (.init newRootVal) hd
    simp only [Nat.zero_add, declSlotData, hnone2, ht] at hset
    refine ⟨newRootVal, withMem m1 (ctx.base ++ localAllocs body.layouts ctx body.localDecls
        (locals.set dst.local_ (.init newRootVal)))
        ⟨.Store, .None, (fieldPtr ctx dst.local_ relOff).addr, ⟨size⟩⟩, hwpath, hwsem, ?_, ?_⟩
    · have hst' := hst
      simp only [localAllocs, TupleSpec.size] at hst'
      rw [hset] at hst'
      simp [evalStatement, hpeEval, hm1, placeStore, hst', localAllocs]
    refine ⟨h.hf, withMem_shape h1.shape _, by simp [h.nlocals], ?_, h.addrs, h.declsOk⟩
    · intro j d' slot' hd' hs''
      by_cases hij : dst.local_ = j
      · subst hij
        rw [hd] at hd'; cases hd'
        simp [List.getElem?_set_self (by rw [h.nlocals]; exact hj)] at hs''
        subst hs''
        simp only [DeclSlotOk, hnone2, ht]
        exact ⟨hrootWf, hnewRootOk⟩
      · rw [List.getElem?_set_ne hij] at hs''
        exact h.slots j d' slot' hd' hs''
  · obtain ⟨msg, hmsg⟩ := hrnone hnone
    exact ⟨msg, by simp [evalStatement, hpeEval, hmsg]⟩

/-- `Machine::eval_statement` on a translated fragment scalar field assignment `_i.f1...fk = rv`. -/
theorem evalStatement_assign_field_scalar {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} {targetTy : Option MirAst.Ty}
    (h : FrameOk body f ctx locals m blk stmt)
    (i idx : Nat) (fieldTy : MirAst.Ty) (rest : List ProjectionElem)
    (it : Gen.IntType)
    (hpok : placeOk body.layouts body.localDecls it ⟨i, .field idx fieldTy :: rest⟩ = true)
    (pe : Gen.PlaceExpr) (hpe : translatePlace body.localDecls ⟨i, .field idx fieldTy :: rest⟩ = some pe)
    (rv : Rvalue) (hok : rvalueOk body.layouts body.localDecls it rv = true)
    (e : Gen.ValueExpr) (he : translateRvalue body.layouts body.localDecls targetTy rv = some e)
    (rootVal : Value) (hs : locals[i]? = some (.init rootVal)) :
    (∀ r, rvBits body.localDecls locals it body.layouts rv = some r →
      ∃ newRootVal m',
        writeFieldPath rootVal (.field idx fieldTy :: rest) (.scalar ⟨r, it.size.bytes⟩) = some newRootVal ∧
        (∀ locals', MirSemantics.writeProjectedValue locals' rootVal (.field idx fieldTy :: rest)
          (.scalar ⟨r, it.size.bytes⟩) = .ok newRootVal) ∧
        evalStatement m (.Assign pe e) = .ok m' ∧
        FrameOk body f ctx (locals.set i (.init newRootVal)) m' blk stmt) ∧
    (rvBits body.localDecls locals it body.layouts rv = none →
      ∃ msg, evalStatement m (.Assign pe e) = .error (.ub msg)) := by
  simp only [placeOk, Bool.and_eq_true, decide_eq_true_eq] at hpok
  obtain ⟨hi, hpok⟩ := hpok
  cases hd : body.localDecls[i]? with
  | none => simp [hd] at hpok
  | some d =>
    simp only [hd, Option.bind_eq_bind, Option.bind_some] at hpok
    cases ht : tupleTypeOf body.layouts d.ty with
    | none => simp [ht] at hpok
    | some rpair =>
      obtain ⟨rootFields, rootSize, rootAlign⟩ := rpair
      simp only [ht] at hpok
      cases hres : resolveFieldPath body.layouts (.tuple rootFields rootSize rootAlign)
          (.field idx fieldTy :: rest) with
      | none => simp [hres] at hpok
      | some lpair =>
        obtain ⟨relOff, leafSpec⟩ := lpair
        simp only [hres] at hpok
        cases leafSpec with
        | tuple _ _ _ => simp at hpok
        | scalar leafIt =>
          simp only [decide_eq_true_eq] at hpok
          subst hpok
          simp only [translatePlace] at hpe
          have hnone1 := intTypeOf_none_of_tupleTypeOf ht
          have hnone2 := arrayTypeOf_none_of_tupleTypeOf ht
          have hslot := h.slots i d (.init rootVal) hd hs
          simp only [DeclSlotOk, hnone2, ht] at hslot
          obtain ⟨hrootWf, hrootVal⟩ := hslot
          obtain ⟨hleafWf, hrelBound⟩ := resolveFieldPath_wf hrootWf hres
          have hgood : GoodSize leafIt.size.bytes := by
            simp only [TupleSpec.wf] at hleafWf
            exact (goodAlignBytes_iff leafIt.size.bytes).mp hleafWf
          have htr : translateTy body.layouts d.ty =
              some ((TupleSpec.tuple rootFields rootSize rootAlign).toMiniRustTy) := by
            simp [translateTy, hnone1, hnone2, ht]
          have hspec := translateFn_local_ty h.hf i d _ hd htr
          have hplaceBase := evalPlace_local h.shape i hi _ hspec
          have hL := h.localAllocs_get i d (.init rootVal) hd hs
          simp only [declSlotData, hnone2, ht] at hL
          have hdlen : ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal).length = rootSize :=
            TupleSpec.encodeVal_length (.tuple rootFields rootSize rootAlign) rootVal hrootWf
          have hbound : rootSize < 2 ^ 63 := by
            simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hrootWf
            exact hrootWf.1.2
          have haddr := h.addrs i d hd
          simp only [AddrOk, hnone2, ht] at haddr
          obtain ⟨_, haddr0, haddrMax⟩ := haddr
          have hrootEval : evalPlace m (.Local (localName i)) =
              .ok (({ ptr := { thin_pointer := fieldPtr ctx i 0, metadata := none },
                       aligned := true },
                     (TupleSpec.tuple rootFields rootSize rootAlign).toMiniRustTy), m) := by
            simpa using hplaceBase
          have hpeEval := evalPlace_fieldPath h.shape i (itOf body.layouts d)
            ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal) hL
            (by rw [hdlen]; exact hbound) haddr0 (by rw [hdlen]; exact haddrMax)
            (.Local (localName i)) 0 (.tuple rootFields rootSize rootAlign) hrootEval hrootWf
            (by simp [TupleSpec.size, hdlen]) (.field idx fieldTy :: rest) pe hpe
            relOff (.scalar leafIt) hres
          simp only [Nat.zero_add] at hpeEval
          obtain ⟨hrok, hrnone⟩ := evalValue_rvalue h leafIt hgood rv hok e he
          refine ⟨fun r hr => ?_, fun hnone => ?_⟩
          · obtain ⟨hrlt, m1, hm1, h1⟩ := hrok r hr
            have hnewValOk : (TupleSpec.scalar leafIt).valOk (.scalar ⟨r, leafIt.size.bytes⟩) = true := by
              simp [TupleSpec.valOk, hrlt]
            obtain ⟨newRootVal, hwpath, hnewRootOk, hnewEnc, hwsem⟩ :=
              resolveFieldPath_write hrootWf hrootVal hres hnewValOk
            have hL1 := h1.localAllocs_get i d (.init rootVal) hd hs
            simp only [declSlotData, hnone2, ht] at hL1
            have hst := typedStore_tuple_slice h1.shape i (itOf body.layouts d)
              ((TupleSpec.tuple rootFields rootSize rootAlign).encodeVal rootVal) hL1
              relOff (.scalar leafIt) (.scalar ⟨r, leafIt.size.bytes⟩) hleafWf hnewValOk
              (by rw [hdlen]; exact hrelBound)
            rw [← hnewEnc] at hst
            have hset := localAllocsFrom_set body.layouts ctx 0 body.localDecls locals i d
              (.init newRootVal) hd
            simp only [Nat.zero_add, declSlotData, hnone2, ht] at hset
            refine ⟨newRootVal, withMem m1 (ctx.base ++ localAllocs body.layouts ctx body.localDecls
                (locals.set i (.init newRootVal)))
                ⟨.Store, .None, (fieldPtr ctx i relOff).addr, leafIt.size⟩, hwpath, hwsem, ?_, ?_⟩
            · have hst' := hst
              simp only [localAllocs, TupleSpec.toMiniRustVal, TupleSpec.toMiniRustTy, TupleSpec.size] at hst'
              rw [hset] at hst'
              simp only [TupleSpec.toMiniRustTy] at hpeEval
              simp [evalStatement, hpeEval, hm1, placeStore, hst', localAllocs]
            refine ⟨h.hf, withMem_shape h1.shape _, by simp [h.nlocals], ?_, h.addrs, h.declsOk⟩
            · intro j d' slot' hd' hs''
              by_cases hij : i = j
              · subst hij
                rw [hd] at hd'; cases hd'
                simp [List.getElem?_set_self (by rw [h.nlocals]; exact hi)] at hs''
                subst hs''
                simp only [DeclSlotOk, hnone2, ht]
                exact ⟨hrootWf, hnewRootOk⟩
              · rw [List.getElem?_set_ne hij] at hs''
                exact h.slots j d' slot' hd' hs''
          · obtain ⟨msg, hmsg⟩ := hrnone hnone
            exact ⟨msg, by simp [evalStatement, hpeEval, hmsg]⟩

/-- `Machine::eval_statement` on a translated fragment `PlaceMention`. -/
theorem evalStatement_placeMention {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (hi : i < body.localDecls.length) :
    evalStatement m (.PlaceMention (.Local (localName i))) = .ok m := by
  obtain ⟨d, _, hd, _⟩ := h.slot_exists i hi
  obtain ⟨_, _, hspec⟩ := (translateFn_spec body f h.hf).2.1 i d hd
  have hplace := evalPlace_local h.shape i hi _ hspec
  simp [evalStatement, hplace]

/-- `Machine::eval_statement` on a translated fragment `PlaceMention` of a
nested tuple/struct field projection `⟨i, .field idx fieldTy :: rest⟩` (whether
local `_i` is initialized or uninitialized). -/
theorem evalStatement_placeMention_field {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i idx : Nat) (fieldTy : MirAst.Ty) (rest : List ProjectionElem)
    (pe : Gen.PlaceExpr)
    (hpe : translateFieldPlace (.Local (localName i)) (.field idx fieldTy :: rest) = some pe)
    (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (fields : List (Nat × TupleSpec)) (size align : Nat)
    (ht : tupleTypeOf body.layouts d.ty = some (fields, size, align))
    (relOff : Nat) (leafSpec : TupleSpec)
    (hres : resolveFieldPath body.layouts (.tuple fields size align) (.field idx fieldTy :: rest) =
      some (relOff, leafSpec)) :
    evalStatement m (.PlaceMention pe) = .ok m := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  have hslot := h.slots i d slot hd hs
  have hnone1 := intTypeOf_none_of_tupleTypeOf ht
  have hnone2 := arrayTypeOf_none_of_tupleTypeOf ht
  have htr : translateTy body.layouts d.ty =
      some ((TupleSpec.tuple fields size align).toMiniRustTy) := by
    simp [translateTy, hnone1, hnone2, ht]
  have hspec := translateFn_local_ty h.hf i d _ hd htr
  have hplaceBase := evalPlace_local h.shape i hi _ hspec
  have hL := h.localAllocs_get i d slot hd hs
  have hdlen := declSlotData_length d slot hslot
  simp only [hnone2, ht] at hdlen
  have hrootWf := h.tuple_wf i d fields size align hd ht
  have hbound : size < 2 ^ 63 := by
    simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hrootWf
    exact hrootWf.1.2
  have haddr := h.addrs i d hd
  simp only [AddrOk, hnone2, ht] at haddr
  obtain ⟨_, haddr0, haddrMax⟩ := haddr
  have hrootEval : evalPlace m (.Local (localName i)) =
      .ok (({ ptr := { thin_pointer := fieldPtr ctx i 0, metadata := none },
               aligned := true },
             (TupleSpec.tuple fields size align).toMiniRustTy), m) := by
    simpa using hplaceBase
  have hpeEval := evalPlace_fieldPath h.shape i (itOf body.layouts d)
    (declSlotData body.layouts d slot) hL
    (by rw [hdlen]; exact hbound) haddr0 (by rw [hdlen]; exact haddrMax)
    (.Local (localName i)) 0 (.tuple fields size align) hrootEval hrootWf
    (by simp [TupleSpec.size, hdlen]) (.field idx fieldTy :: rest) pe hpe
    relOff leafSpec hres
  simp [evalStatement, hpeEval]

/-! ## `Switch` -/

theorem intFromBits_inj (it : Gen.IntType) (a b : Nat) (ha : a < 2 ^ (8 * it.size.bytes))
    (hb : b < 2 ^ (8 * it.size.bytes)) : intFromBits a it = intFromBits b it ↔ a = b := by
  constructor
  · intro h
    have := congrArg (· % (2 : Int) ^ (8 * it.size.bytes)) h
    simp only [intFromBits_emod a it ha, intFromBits_emod b it hb] at this
    exact_mod_cast this
  · intro h; rw [h]

theorem switch_lookup (it : Gen.IntType) (bits : Nat) (hb : bits < 2 ^ (8 * it.size.bytes))
    (branches : List (Nat × Nat)) (hbr : ∀ p ∈ branches, p.1 < 2 ^ (8 * it.size.bytes))
    (otherwise : Nat) :
    (mapGet (switchCases it branches) (intFromBits bits it)).getD (bbName otherwise) =
      bbName (MirSemantics.lookupSwitchTarget bits branches otherwise) := by
  induction branches with
  | nil => simp [switchCases, mapGet, MirSemantics.lookupSwitchTarget]
  | cons p ps ih =>
    obtain ⟨v, t⟩ := p
    have hv : v < 2 ^ (8 * it.size.bytes) := hbr (v, t) (by simp)
    have ih' := ih (fun q hq => hbr q (by simp [hq]))
    simp only [switchCases] at ih' ⊢
    rw [List.map_cons, mapGet_cons]
    simp only [MirSemantics.lookupSwitchTarget]
    by_cases hvb : v = bits
    · subst hvb; simp
    · have hne : intFromBits v it ≠ intFromBits bits it := by
        rw [Ne, intFromBits_inj it v bits hv hb]; exact hvb
      have hbeq : Nat.beq bits v = false := by
        cases h : Nat.beq bits v
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h).symm hvb
      simp only [hne, ite_false, hbeq]
      exact ih'

/-! ## `Return` -/

/-- A deallocated allocation (`allocation.live = false`). -/
def kill (a : Gen.Allocation) : Gen.Allocation := { a with live := false }

/-- `L` with the allocations at indices `is` deallocated. -/
def killAt (L : List Gen.Allocation) (is : List Nat) : List Gen.Allocation :=
  L.mapIdx (fun j a => if j ∈ is then kill a else a)

theorem killAt_nil (L : List Gen.Allocation) : killAt L [] = L := by
  apply List.ext_getElem?
  intro j
  simp only [killAt, List.getElem?_mapIdx]
  cases L[j]? <;> simp

theorem killAt_cons (L : List Gen.Allocation) (i : Nat) (is : List Nat) (a : Gen.Allocation)
    (hi : L[i]? = some a) (hni : i ∉ is) :
    killAt L (i :: is) = killAt (L.set i (kill a)) is := by
  apply List.ext_getElem?
  intro j
  simp only [killAt, List.getElem?_mapIdx]
  by_cases hij : i = j
  · subst hij
    simp [hi, hni, List.getElem?_set_self (List.getElem?_eq_some_iff.mp hi).1]
  · simp [List.getElem?_set_ne hij, Ne.symm hij]

theorem killAt_range (L : List Gen.Allocation) : killAt L (List.range L.length) = L.map kill := by
  apply List.ext_getElem?
  intro j
  simp only [killAt, List.getElem?_mapIdx, List.getElem?_map]
  cases h : L[j]? with
  | none => simp
  | some a =>
    have := (List.getElem?_eq_some_iff.mp h).1
    simp [List.mem_range, this]

theorem storageDead_callee {fr : Frame} {cm : Gen.ConcurrentMemory BM} {ctx : Ctx} (i : Nat)
    (rest : List (Gen.LocalName × Ptr)) (hloc : fr.locals = ⟨(localName i, localPtr ctx i) :: rest⟩)
    (hrest : ∀ e ∈ rest, e.1 ≠ localName i) (T : Gen.Type)
    (hty : mapGet fr.func.locals (localName i) = some T) (L' : List Gen.Allocation)
    (hmem : cm.memory.allocations = ctx.base ++ L') (a : Gen.Allocation) (ha : L'[i]? = some a)
    (hlive : a.live = true) (haddr : a.addr = ctx.addrs.getD i 0) (hkind : a.kind = .Stack)
    (hlay : Type.layout T = .ok (.Sized ⟨a.data.length⟩ a.align)) :
    storageDead fr cm (localName i) =
      .ok ({ fr with locals := ⟨rest⟩ },
           { cm with memory := { cm.memory with allocations := ctx.base ++ L'.set i (kill a) } }) := by
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp ha
  have hrest' : ∀ (x : Gen.LocalName) (y : Gen.ThinPointer (Gen.Memory.Provenance BM)),
      (x, y) ∈ rest → ¬x = localName i :=
    fun x y hxy => hrest (x, y) hxy
  simp [storageDead, mapIndex, hty, hlay, LayoutStrategy.expect_size,
    LayoutStrategy.expect_align, mapRemove, hloc, mapGet_cons, CM.deallocate,
    BM.deallocate, localPtr, listIndex, hmem, hi, hai, hlive, haddr, hkind, Allocation.size,
    listSet, kill]
  exact hrest'

theorem deallocAll_callee (ctx : Ctx) (fuel : Nat) (fr : Frame) (cm : Gen.ConcurrentMemory BM)
    (is : List Nat) (L' : List Gen.Allocation) (hfuel : is.length ≤ fuel)
    (hloc : fr.locals = ⟨is.map (fun i => (localName i, localPtr ctx i))⟩) (hnodup : is.Nodup)
    (hmem : cm.memory.allocations = ctx.base ++ L')
    (hok : ∀ i ∈ is, ∃ T a, mapGet fr.func.locals (localName i) = some T ∧
      L'[i]? = some a ∧ a.live = true ∧ a.addr = ctx.addrs.getD i 0 ∧
      a.kind = .Stack ∧ Type.layout T = .ok (.Sized ⟨a.data.length⟩ a.align)) :
    ∃ cm', deallocAll fuel fr cm = .ok ({ fr with locals := ⟨[]⟩ }, cm') ∧
      cm'.memory.allocations = ctx.base ++ killAt L' is := by
  induction is generalizing fuel fr cm L' with
  | nil =>
    refine ⟨cm, ?_, by simp [hmem, killAt_nil]⟩
    have hfr : fr = { fr with locals := ⟨[]⟩ } := by
      cases fr; simp at hloc; simp [hloc]
    cases fuel <;> (simp only [deallocAll, hloc, List.map_nil]; rw [← hfr]; rfl)
  | cons i is ih =>
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    simp only [List.nodup_cons] at hnodup
    obtain ⟨hni, hnd⟩ := hnodup
    obtain ⟨T, a, hty, ha, hlive, haddr, hkind, hlay⟩ := hok i (by simp)
    have hrest : ∀ e ∈ is.map (fun i => (localName i, localPtr ctx i)), e.1 ≠ localName i := by
      intro e he
      simp only [List.mem_map] at he
      obtain ⟨j, hj, rfl⟩ := he
      simp only [ne_eq, localName_inj]
      intro hji; subst hji; exact hni hj
    have hsd := storageDead_callee i _ (by simpa using hloc) hrest T hty L' hmem a ha hlive
      haddr hkind hlay
    obtain ⟨cm', hcm', hcm'mem⟩ := ih fuel' { fr with locals := ⟨is.map (fun i => (localName i, localPtr ctx i))⟩ }
      { cm with memory := { cm.memory with allocations := ctx.base ++ L'.set i (kill a) } }
      (L'.set i (kill a)) (by simp at hfuel; omega) rfl hnd rfl
      (by
        intro j hj
        obtain ⟨T', a', hty', ha', h1, h2, h3, h4⟩ := hok j (by simp [hj])
        have hij : i ≠ j := fun h => hni (h ▸ hj)
        exact ⟨T', a', hty', by rw [List.getElem?_set_ne hij]; exact ha', h1, h2, h3, h4⟩)
    refine ⟨cm', ?_, ?_⟩
    · rw [deallocAll]
      simp only [hloc, List.map_cons]
      rw [hsd]
      simpa using hcm'
    · rw [hcm'mem, killAt_cons L' i is a ha hni]

theorem typedStore_base {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (p : Ptr) (r : Nat) (a : Gen.Allocation)
    (hp : p.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a) (hlive : a.live = true)
    (haddr : a.addr = p.addr) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (hlen : a.data.length = it.size.bytes) (v : Int) (hv : IntType.can_represent it v = true)
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    typedStore m p (.Int v) (.Int it) align .None =
      .ok (withMem m (ctx.base.set r { a with data := scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat } ++ L)
            ⟨.Store, .None, p.addr, it.size⟩) := by
  have hpos := hgood.pos
  obtain ⟨hri, hai⟩ := List.getElem?_eq_some_iff.mp hr
  have hblen : (scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat).length = it.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hck : checkValue (.Int v) (.Int it) = .ok () := by simp [checkValue, hv]
  have hne : scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  have hdrop : a.data.drop it.size.bytes = [] := List.drop_eq_nil_of_le (by omega)
  have hrlt : r < ctx.base.length + L.length := by omega
  simp only [typedStore, hck, encode_int it v hgood hv, CM.store, BM.store, hal, BM.check_ptr, hp,
    listIndex, h.allocs]
  obtain ⟨signed, size⟩ := it
  simp [hne, hlive, haddr, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem,
    hdrop, List.set_append_left _ _ hri, hri, hrlt, hai]

end MiniRustSpec.Correspondence
