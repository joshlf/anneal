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

/-! ## The callee's allocations and locals map -/

theorem slotData_length (it : Gen.IntType) (slot : LocalSlot) :
    (slotData it slot).length = it.size.bytes := by
  unfold slotData
  split <;> simp [scalarBytes, uninitBytes, leBytes_length]

theorem localAllocsFrom_getElem? (ctx : Ctx) (k : Nat) (ds : List LocalDecl) (slots : List LocalSlot)
    (j : Nat) (d : LocalDecl) (slot : LocalSlot) (hd : ds[j]? = some d) (hs : slots[j]? = some slot) :
    (localAllocsFrom ctx k ds slots)[j]? =
      some (localAlloc ctx (k + j) (itOf d) (slotData (itOf d) slot)) := by
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

theorem localAllocsFrom_set (ctx : Ctx) (k : Nat) (ds : List LocalDecl) (slots : List LocalSlot)
    (j : Nat) (d : LocalDecl) (slot' : LocalSlot) (hd : ds[j]? = some d) :
    (localAllocsFrom ctx k ds slots).set j (localAlloc ctx (k + j) (itOf d) (slotData (itOf d) slot')) =
      localAllocsFrom ctx k ds (slots.set j slot') := by
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

theorem localAllocsFrom_length (ctx : Ctx) (k : Nat) (ds : List LocalDecl) (slots : List LocalSlot) :
    (localAllocsFrom ctx k ds slots).length = min ds.length slots.length := by
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
theorem isAligned_one (a : Int) : Align.is_aligned ⟨1⟩ a = true := by
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

/-! ## `bool` locals

A `bool` local is stored like a `u8` local (`u8Ty`: one byte, alignment one);
its byte must be `0` or `1` to decode at `Type::Bool`. -/

theorem layout_bool : Type.layout .Bool = .ok (.Sized u8Ty.size ⟨u8Ty.size.bytes⟩) := rfl

theorem scalarBytes_u8 (bits : Nat) :
    scalarBytes u8Ty bits = [.Init (UInt8.ofNat (bits % 256)) none] := by
  simp [scalarBytes, u8Ty, leBytes]

theorem decode_bool (bits : Nat) (hb : bits < 2) :
    Type.decode .Bool (scalarBytes u8Ty bits) = .ok (some (.Bool (decide (bits = 1)))) := by
  rcases (by omega : bits = 0 ∨ bits = 1) with rfl | rfl <;> rfl

theorem encode_bool (b : Bool) :
    Type.encode .Bool (.Bool b) = .ok (scalarBytes u8Ty (if b then 1 else 0)) := by
  cases b <;> rfl

theorem typedLoad_local_bool {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (bits : Nat) (hb : bits < 2)
    (hL : L[i]? = some (localAlloc ctx i u8Ty (scalarBytes u8Ty bits)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) .Bool align .None = .ok (.Bool (decide (bits = 1)), m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hlen : (scalarBytes u8Ty bits).length = u8Ty.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD i 0, u8Ty.size⟩, ?_,
    withMem_shape h _⟩
  simp only [typedLoad, layout_bool, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [hu8, hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset,
    List.take_of_length_le, decode_bool bits hb, checkValue, withMem]

theorem typedLoad_local_bool_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat)
    (hL : L[i]? = some (localAlloc ctx i u8Ty (uninitBytes u8Ty)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) .Bool align .None = .error (.ub msg) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hlen : (uninitBytes u8Ty).length = u8Ty.size.bytes := by simp [uninitBytes]
  have hdec : Type.decode .Bool (uninitBytes u8Ty) = .ok none := rfl
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨"load at type but the data in memory violates the language invariant", ?_⟩
  simp only [typedLoad, layout_bool, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [hu8, hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset,
    List.take_of_length_le, hdec, ub]

theorem typedStore_local_bool {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (data : List Byte) (b : Bool)
    (hL : L[i]? = some (localAlloc ctx i u8Ty data)) (hlen : data.length = u8Ty.size.bytes)
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    typedStore m (localPtr ctx i) (.Bool b) .Bool align .None =
      .ok (withMem m (ctx.base ++ L.set i
              (localAlloc ctx i u8Ty (scalarBytes u8Ty (if b then 1 else 0))))
            ⟨.Store, .None, ctx.addrs.getD i 0, u8Ty.size⟩) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hck : checkValue (.Bool b) .Bool = .ok () := rfl
  have hblen : (scalarBytes u8Ty (if b then 1 else 0)).length = u8Ty.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hne : scalarBytes u8Ty (if b then 1 else 0) ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hblen, hu8]; omega)
  have hdrop : data.drop u8Ty.size.bytes = [] := List.drop_eq_nil_of_le (by omega)
  simp only [typedStore, hck, encode_bool, CM.store, BM.store, hal, BM.check_ptr, localPtr,
    listIndex, h.allocs]
  simp [hne, hi, hLi, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem, hdrop]
  simp [localAlloc, hu8]

/-! ## Fragment types

`FragTy T it` says that `T` is a fragment type stored like the integer type
`it`: an integer type of good size is stored as itself, and `bool` as `u8`. -/

/-- Fragment types and their storage integer types. -/
inductive FragTy : Gen.Type → Gen.IntType → Prop
  | int (it : Gen.IntType) (h : GoodSize it.size.bytes) : FragTy (.Int it) it
  | bool : FragTy .Bool u8Ty

/-- The MiniRust value that the bit pattern `bits` encodes at fragment type
`T`. -/
def valOf : Gen.Type → Nat → Val
  | .Int it, bits => .Int (intFromBits bits it)
  | .Bool, bits => .Bool (decide (bits = 1))
  | _, _ => .Int 0

theorem FragTy.good {T : Gen.Type} {it : Gen.IntType} (h : FragTy T it) : GoodSize it.size.bytes := by
  cases h with
  | int _ h => exact h
  | bool => simp [u8Ty, GoodSize]

theorem FragTy.layout {T : Gen.Type} {it : Gen.IntType} (h : FragTy T it) :
    Type.layout T = .ok (.Sized it.size ⟨it.size.bytes⟩) := by
  cases h with
  | int _ h => exact layout_eq _ h
  | bool => exact layout_bool

theorem FragTy.tyBytes {T : Gen.Type} {it : Gen.IntType} (h : FragTy T it) :
    tyBytes T = it.size.bytes := by
  cases h <;> rfl

theorem FragTy.validBits_lt {T : Gen.Type} {it : Gen.IntType} (h : FragTy T it) {bits : Nat}
    (hb : ValidBits T bits) : bits < 2 ^ (8 * it.size.bytes) := by
  cases h with
  | int _ _ => exact hb
  | bool => simp [ValidBits] at hb; simp [u8Ty]; omega

/-- A fragment local's declared MiniRust type is a fragment type stored like
`itOf d`. -/
theorem fragTy_of_decl {d : LocalDecl} (h : scalarTypeOf d.ty = some (tyOf d)) :
    FragTy (tyOf d) (itOf d) := by
  rcases scalarTypeOf_cases h with ⟨hb, _⟩ | ⟨it, hit, _⟩
  · obtain ⟨h1, h2⟩ := tyOf_bool hb; rw [h1, h2]; exact .bool
  · obtain ⟨h1, h2⟩ := tyOf_int hit; rw [h1, h2]; exact .int it (intTypeOf_good hit)

theorem typedLoad_local_frag {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) {T : Gen.Type} {it : Gen.IntType}
    (hT : FragTy T it) (bits : Nat) (hb : ValidBits T bits)
    (hL : L[i]? = some (localAlloc ctx i it (scalarBytes it bits)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) T align .None = .ok (valOf T bits, m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  cases hT with
  | int it hgood => exact typedLoad_local_init h i it bits hgood hb hL align hal
  | bool => exact typedLoad_local_bool h i bits (by simpa [ValidBits] using hb) hL align hal

theorem typedLoad_local_frag_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) {T : Gen.Type}
    {it : Gen.IntType} (hT : FragTy T it) (hL : L[i]? = some (localAlloc ctx i it (uninitBytes it)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) T align .None = .error (.ub msg) := by
  cases hT with
  | int it hgood => exact typedLoad_local_uninit h i it hgood hL align hal
  | bool => exact typedLoad_local_bool_uninit h i hL align hal

theorem typedStore_local_frag {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) {T : Gen.Type} {it : Gen.IntType}
    (hT : FragTy T it) (data : List Byte) (bits : Nat) (hb : ValidBits T bits)
    (hL : L[i]? = some (localAlloc ctx i it data)) (hlen : data.length = it.size.bytes)
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    typedStore m (localPtr ctx i) (valOf T bits) T align .None =
      .ok (withMem m (ctx.base ++ L.set i (localAlloc ctx i it (scalarBytes it bits)))
            ⟨.Store, .None, ctx.addrs.getD i 0, it.size⟩) := by
  cases hT with
  | int it hgood =>
    have hb' : bits < 2 ^ (8 * it.size.bytes) := hb
    have hst := typedStore_local h i it data (intFromBits bits it) hgood hL hlen
      (canRepresent_intFromBits it bits hgood hb') align hal
    have hres : (intFromBits bits it % 2 ^ (8 * it.size.bytes)).toNat = bits := by
      rw [intFromBits_emod bits _ hb']; simp
    rw [hres] at hst
    exact hst
  | bool =>
    have hb' : bits < 2 := by simpa [ValidBits] using hb
    have hst := typedStore_local_bool h i data (decide (bits = 1)) hL hlen align hal
    have hres : (if decide (bits = 1) then 1 else 0) = bits := by
      rcases (by omega : bits = 0 ∨ bits = 1) with rfl | rfl <;> rfl
    rw [hres] at hst
    exact hst

/-! ## Places of the callee's locals -/

theorem evalPlace_local {m : Mach} {ctx : Ctx} {f : Gen.Function} {n blk stmt : Nat}
    {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrame f ctx n blk stmt] allocs) (i : Nat) (hi : i < n)
    (T : Gen.Type) (hT : mapGet f.locals (localName i) = some T) :
    evalPlace m (.Local (localName i)) =
      .ok ({ ptr := { thin_pointer := localPtr ctx i, metadata := none }, aligned := true }, T) := by
  simp [evalPlace, curFrame_eq h, mapIndex, calleeFrame, hT, mapGet_localsMap ctx n i hi]

/-! ## Operands and rvalues -/

/-- The bit pattern an Anneal fragment operand evaluates to, or `none` when
reading it is UB (an uninitialized local). -/
def opBits (locals : List LocalSlot) : Operand → Option Nat
  | .copy ⟨j, []⟩ =>
    match locals[j]? with
    | some (.init (.scalar sc)) => some sc.bits
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

theorem operandIntType_of_operandOk {decls : List LocalDecl} {it : Gen.IntType} {op : Operand}
    (h : operandOk decls it op = true) : operandIntType decls op = some it := by
  match op, h with
  | .copy ⟨_, []⟩, h =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  | .constant _, h =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

theorem rvalueOk_binaryOp {decls : List LocalDecl} {it : Gen.IntType}
    {op : MirAst.BinOp} {a b : Operand}
    (h : rvalueOk decls it (.binaryOp op a b) = true) :
    ∃ iop rhsIt,
      translateBinOp op = some iop ∧
      operandOk decls it a = true ∧
      operandIntType decls b = some rhsIt ∧
      operandOk decls rhsIt b = true ∧
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
      cases hrhs : operandIntType decls b with
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
    (ctx.base ++ localAllocs ctx body.localDecls locals)
  nlocals : locals.length = body.localDecls.length
  slots : ∀ (i : Nat) d slot, body.localDecls[i]? = some d → locals[i]? = some slot →
    SlotOk (tyOf d) slot

theorem FrameOk.decl_frag {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) : FragTy (tyOf d) (itOf d) :=
  fragTy_of_decl ((translateFn_spec body f h.hf).2.1 i d hd).1

theorem FrameOk.decl_good {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {locals : List LocalSlot}
    {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt) (i : Nat) (d : LocalDecl)
    (hd : body.localDecls[i]? = some d) : GoodSize (itOf d).size.bytes :=
  (h.decl_frag i d hd).good

theorem FrameOk.localAllocs_get {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (_h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (slot : LocalSlot) (hd : body.localDecls[i]? = some d)
    (hs : locals[i]? = some slot) :
    (localAllocs ctx body.localDecls locals)[i]? =
      some (localAlloc ctx i (itOf d) (slotData (itOf d) slot)) := by
  simpa [localAllocs] using localAllocsFrom_getElem? ctx 0 body.localDecls locals i d slot hd hs

theorem FrameOk.slot_exists {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (hi : i < body.localDecls.length) :
    ∃ d slot, body.localDecls[i]? = some d ∧ locals[i]? = some slot := by
  refine ⟨body.localDecls[i], locals[i]'(by rw [h.nlocals]; exact hi), by simp [hi], by simp⟩

theorem FragTy.unique {T : Gen.Type} {it it' : Gen.IntType} (h : FragTy T it) (h' : FragTy T it') :
    it = it' := by
  cases h <;> cases h' <;> rfl

/-- A projection-free fragment operand of MiniRust type `T`: the common shape
of `operandOk` (integers) and `operandOkB` (`bool`). -/
def OperandOkT (decls : List LocalDecl) (T : Gen.Type) : Operand → Prop
  | .copy ⟨j, []⟩ => j < decls.length ∧ operandType decls (.copy ⟨j, []⟩) = some T
  | .constant c => operandType decls (.constant c) = some T ∧ (translateOperand (.constant c)).isSome
  | _ => False

theorem operandType_of_operandIntType {decls : List LocalDecl} {it : Gen.IntType} {op : Operand}
    (h : operandIntType decls op = some it) : operandType decls op = some (.Int it) := by
  match op, h with
  | .copy ⟨j, []⟩, h =>
    simp only [operandIntType] at h
    simp only [operandType]
    cases hd : decls[j]? with
    | none => simp [hd] at h
    | some d => simp [hd] at h ⊢; exact scalarTypeOf_int h
  | .constant c, h => simp only [operandIntType] at h; exact scalarTypeOf_int h

theorem operandOk_T {decls : List LocalDecl} {it : Gen.IntType} {op : Operand}
    (h : operandOk decls it op = true) : OperandOkT decls (.Int it) op := by
  match op, h with
  | .copy ⟨j, []⟩, h =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, operandType_of_operandIntType h.2⟩
  | .constant c, h =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨operandType_of_operandIntType h.1, h.2⟩

theorem operandIsBool_iff {decls : List LocalDecl} {op : Operand} :
    operandIsBool decls op = true ↔ operandType decls op = some .Bool := by
  unfold operandIsBool
  split <;> simp_all

theorem operandOkB_T {decls : List LocalDecl} {op : Operand}
    (h : operandOkB decls op = true) : OperandOkT decls .Bool op := by
  match op, h with
  | .copy ⟨j, []⟩, h =>
    simp only [operandOkB, Bool.and_eq_true, decide_eq_true_eq, operandIsBool_iff] at h
    exact h
  | .constant c, h =>
    simp only [operandOkB, Bool.and_eq_true, operandIsBool_iff] at h
    exact h

/-- Evaluating a translated fragment operand of fragment type `T`. -/
theorem evalValue_operandT {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    {T : Gen.Type} {it : Gen.IntType} (hT : FragTy T it) (op : Operand)
    (hok : OperandOkT body.localDecls T op) (e : Gen.ValueExpr) (he : translateOperand op = some e) :
    (∀ bits, opBits locals op = some bits →
      ValidBits T bits ∧
      ∃ m', evalValue m e = .ok ((valOf T bits, T), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (opBits locals op = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  match op, hok, he with
  | .copy ⟨j, []⟩, hok, he =>
    obtain ⟨hj, hty⟩ := hok
    simp only [translateOperand, Option.some.injEq] at he
    subst he
    obtain ⟨d, slot, hd, hs⟩ := h.slot_exists j hj
    have hspec := (translateFn_spec body f h.hf).2.1 j d hd
    have hTd : tyOf d = T := by
      simp only [operandType, hd] at hty
      rw [tyOf_of_scalarTypeOf hty]
    have hitd : itOf d = it := (h.decl_frag j d hd).unique (hTd ▸ hT)
    have hloc := hspec.2
    rw [hTd] at hloc
    have hplace := evalPlace_local h.shape j hj _ hloc
    have hL := h.localAllocs_get j d slot hd hs
    rw [hitd] at hL
    have hslot := h.slots j d slot hd hs
    rw [hTd] at hslot
    match slot, hslot, hL with
    | .uninit, _, hL =>
      refine ⟨fun bits hb => by simp [opBits, hs] at hb, fun _ => ?_⟩
      obtain ⟨msg, hmsg⟩ := typedLoad_local_frag_uninit h.shape j hT hL ⟨1⟩ (isAligned_one _)
      exact ⟨msg, by simp [evalValue, hplace, placeLoad, hmsg]⟩
    | .init (.scalar sc), hok', hL =>
      obtain ⟨_, hb⟩ := hok'
      refine ⟨fun bits hbits => ?_, fun hnone => by simp [opBits, hs] at hnone⟩
      simp [opBits, hs] at hbits
      subst hbits
      obtain ⟨m', hm', hshape⟩ :=
        typedLoad_local_frag h.shape j hT sc.bits hb hL ⟨1⟩ (isAligned_one _)
      exact ⟨hb, m', by simp [evalValue, hplace, placeLoad, hm'],
        ⟨h.hf, hshape, h.nlocals, h.slots⟩⟩
  | .constant c, hok, he =>
    obtain ⟨hty, _⟩ := hok
    simp only [operandType] at hty
    rcases scalarTypeOf_cases hty with ⟨hb, hTb⟩ | ⟨it', hit', hTi⟩
    · subst hTb
      simp only [translateOperand, hb, ↓reduceIte] at he
      match hv : c.val, he with
      | .scalar (.int ⟨bits, sz⟩), he =>
        simp only at he
        split at he
        · next hc =>
          simp only [Option.some.injEq] at he
          subst he
          obtain ⟨_, hb2⟩ := hc
          refine ⟨fun bits' hbits => ?_, fun hnone => by simp [opBits, hv] at hnone⟩
          simp [opBits, hv] at hbits
          subst hbits
          exact ⟨hb2, m, by simp [evalValue, evalConstant, valOf], h⟩
        · simp at he
    · subst hTi
      simp only [translateOperand, intTypeOf_isBoolTy hit', hit', Bool.false_eq_true,
        ↓reduceIte] at he
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
          exact ⟨hb, m, by simp [evalValue, evalConstant, valOf], h⟩
        · simp at he

theorem operandOk_good {decls : List LocalDecl} {it : Gen.IntType} {op : Operand}
    (hok : operandOk decls it op = true) : GoodSize it.size.bytes := by
  have hit := operandIntType_of_operandOk hok
  match op, hit with
  | .copy ⟨j, []⟩, hit =>
    simp only [operandIntType] at hit
    cases hd : decls[j]? with
    | none => simp [hd] at hit
    | some d => simp [hd] at hit; exact intTypeOf_good hit
  | .constant c, hit => simp only [operandIntType] at hit; exact intTypeOf_good hit

/-- Evaluating a translated fragment operand of integer type `it`. -/
theorem evalValue_operand {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (it : Gen.IntType) (op : Operand) (hok : operandOk body.localDecls it op = true)
    (e : Gen.ValueExpr) (he : translateOperand op = some e) :
    (∀ bits, opBits locals op = some bits →
      bits < 2 ^ (8 * it.size.bytes) ∧
      ∃ m', evalValue m e = .ok ((.Int (intFromBits bits it), .Int it), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (opBits locals op = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  have hokT := operandOk_T hok
  have hgood : GoodSize it.size.bytes := operandOk_good hok
  exact evalValue_operandT h (.int it hgood) op hokT e he

/-- The bit pattern an Anneal fragment rvalue of type `it` evaluates to, or
`none` when evaluating it is UB. -/
def rvBits (decls : List LocalDecl) (locals : List LocalSlot) (it : Gen.IntType) : Rvalue → Option Nat
  | .use op => opBits locals op
  | .unaryOp uop op => do
    let iuop ← translateUnOp uop
    let x ← opBits locals op
    pure (intUnArith iuop x % 2 ^ (8 * it.size.bytes)).toNat
  | .binaryOp op a b => do
    let iop ← translateBinOp op
    let rhsIt ← operandIntType decls b
    let x ← opBits locals a
    let y ← opBits locals b
    let z ← intBinEval iop (intFromBits x it) (intFromBits y rhsIt) it
    pure (z % 2 ^ (8 * it.size.bytes)).toNat
  | .cast .intToInt op _ => do
    let srcIt := (operandIntType decls op).getD u8Ty
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

theorem translateRelOp_of_translateBinOp {op : MirAst.BinOp} {iop : Gen.IntBinOp}
    (h : translateBinOp op = some iop) : translateRelOp op = none := by
  cases op <;> simp_all [translateBinOp, translateRelOp]

theorem translateRvalue_unary_int {decls : List LocalDecl} {it : Gen.IntType} {uop : MirAst.UnOp}
    {op : Operand} {e : Gen.ValueExpr} (hok : operandOk decls it op = true)
    (he : translateRvalue decls (.unaryOp uop op) = some e) :
    ∃ iuop eo, translateUnOp uop = some iuop ∧ translateOperand op = some eo ∧
      e = .UnOp (.Int iuop) eo := by
  have hty := operandType_of_operandIntType (operandIntType_of_operandOk hok)
  simp only [translateRvalue, Option.bind_eq_bind] at he
  cases heo : translateOperand op with
  | none => simp [heo] at he
  | some eo =>
    simp only [heo, Option.bind_some, hty] at he
    cases hu : translateUnOp uop with
    | none => simp [hu] at he
    | some iuop => simp [hu] at he; exact ⟨iuop, eo, rfl, rfl, he.symm⟩

theorem translateRvalue_binary_int {decls : List LocalDecl} {it : Gen.IntType} {op : MirAst.BinOp}
    {a b : Operand} {e : Gen.ValueExpr} {iop : Gen.IntBinOp} (hiop : translateBinOp op = some iop)
    (hok : operandOk decls it a = true) (he : translateRvalue decls (.binaryOp op a b) = some e) :
    ∃ ea eb, translateOperand a = some ea ∧ translateOperand b = some eb ∧
      e = .BinOp (.Int iop) ea eb := by
  have hty := operandType_of_operandIntType (operandIntType_of_operandOk hok)
  simp only [translateRvalue, Option.bind_eq_bind, translateRelOp_of_translateBinOp hiop] at he
  cases hea : translateOperand a with
  | none => simp [hea] at he
  | some ea =>
    cases heb : translateOperand b with
    | none => simp [hea, heb] at he
    | some eb =>
      simp only [hea, heb, Option.bind_some, hty, hiop] at he
      simp at he
      exact ⟨ea, eb, rfl, rfl, he.symm⟩

/-- `build::bool_to_int::<u8>` (a transmute to `u8`) maps `false`/`true` to
`0`/`1`. -/
theorem evalValue_boolToU8 (m m1 : Mach) (e : Gen.ValueExpr) (b : Bool)
    (he : evalValue m e = .ok ((.Bool b, .Bool), m1)) :
    evalValue m (boolToU8 e) = .ok ((.Int (if b then 1 else 0), .Int u8Ty), m1) := by
  cases b <;> simp [boolToU8, evalValue, he, evalUnOp] <;> rfl

theorem translateRvalue_cast_int {decls : List LocalDecl} {srcIt it : Gen.IntType} {op : Operand}
    {targetTy : MirAst.Ty} {e : Gen.ValueExpr} (htgt : intTypeOf targetTy = some it)
    (hok : operandOk decls srcIt op = true)
    (he : translateRvalue decls (.cast .intToInt op targetTy) = some e) :
    ∃ eo, translateOperand op = some eo ∧ e = .UnOp (.Cast (.IntToInt it)) eo := by
  have hty := operandType_of_operandIntType (operandIntType_of_operandOk hok)
  simp only [translateRvalue, Option.bind_eq_bind, htgt, Option.bind_some] at he
  cases heo : translateOperand op with
  | none => simp [heo] at he
  | some eo =>
    simp only [heo, Option.bind_some, hty] at he
    simp at he
    exact ⟨eo, rfl, he.symm⟩

theorem translateRvalue_cast_bool {decls : List LocalDecl} {it : Gen.IntType} {op : Operand}
    {targetTy : MirAst.Ty} {e : Gen.ValueExpr} (htgt : intTypeOf targetTy = some it)
    (hok : operandOkB decls op = true)
    (he : translateRvalue decls (.cast .intToInt op targetTy) = some e) :
    ∃ eo, translateOperand op = some eo ∧ e = .UnOp (.Cast (.IntToInt it)) (boolToU8 eo) := by
  have hty : operandType decls op = some .Bool := by
    match op, hok with
    | .copy ⟨j, []⟩, hok =>
      simp only [operandOkB, Bool.and_eq_true, decide_eq_true_eq, operandIsBool_iff] at hok
      exact hok.2
    | .constant c, hok =>
      simp only [operandOkB, Bool.and_eq_true, operandIsBool_iff] at hok
      exact hok.1
  simp only [translateRvalue, Option.bind_eq_bind, htgt, Option.bind_some] at he
  cases heo : translateOperand op with
  | none => simp [heo] at he
  | some eo =>
    simp [heo, hty] at he
    exact ⟨eo, rfl, he.symm⟩

/-- Evaluating a translated fragment rvalue. -/
theorem evalValue_rvalue {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes) (rv : Rvalue)
    (hok : rvalueOk body.localDecls it rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.localDecls rv = some e) :
    (∀ r, rvBits body.localDecls locals it rv = some r →
      r < 2 ^ (8 * it.size.bytes) ∧
      ∃ m', evalValue m e = .ok ((.Int (intFromBits r it), .Int it), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (rvBits body.localDecls locals it rv = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  match rv, hok, he with
  | .use op, hok, he =>
    simp only [rvalueOk] at hok
    simp only [translateRvalue] at he
    exact evalValue_operand h it op hok e he
  | .unaryOp uop op, hok, he =>
    simp only [rvalueOk, Bool.and_eq_true] at hok
    obtain ⟨huop, hok⟩ := hok
    obtain ⟨iuop, eo, hiuop, heo, rfl⟩ := translateRvalue_unary_int hok he
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
    obtain ⟨ea, eb, hea, heb, rfl⟩ := translateRvalue_binary_int hiop hoka he
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
  | .cast .intToInt op targetTy, hok, he =>
    simp only [rvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨htgt, hsrc⟩ := hok
    cases hsrcIt : operandIntType body.localDecls op with
    | none =>
      simp only [hsrcIt] at hsrc
      obtain ⟨eo, heo, rfl⟩ := translateRvalue_cast_bool htgt hsrc he
      obtain ⟨haok, hanone⟩ := evalValue_operandT h .bool op (operandOkB_T hsrc) eo heo
      cases hxo : opBits locals op with
      | none =>
        refine ⟨fun r hr => by simp [rvBits, hsrcIt, hxo] at hr, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hanone hxo
        exact ⟨msg, by simp [boolToU8, evalValue, hmsg]⟩
      | some x =>
        obtain ⟨hvx, m1, hm1, h1⟩ := haok x hxo
        have hx2 : x < 2 := by simpa [ValidBits] using hvx
        refine ⟨fun r hr => ?_, fun hnone => by simp [rvBits, hsrcIt, hxo] at hnone⟩
        simp [rvBits, hsrcIt, hxo] at hr
        subst hr
        have hpos := two_pow_pos (8 * it.size.bytes)
        have hlt : (intFromBits x u8Ty % 2 ^ (8 * it.size.bytes)).toNat < 2 ^ (8 * it.size.bytes) := by
          have h0 := Int.emod_nonneg (intFromBits x u8Ty) (Int.ne_of_gt hpos)
          have hlt' := Int.emod_lt_of_pos (intFromBits x u8Ty) hpos
          have : (((intFromBits x u8Ty % 2 ^ (8 * it.size.bytes)).toNat : Int)) < 2 ^ (8 * it.size.bytes) := by
            rw [Int.toNat_of_nonneg h0]; exact hlt'
          exact_mod_cast this
        refine ⟨hlt, m1, ?_, h1⟩
        have h8 := evalValue_boolToU8 m m1 eo (decide (x = 1)) (by simpa [valOf] using hm1)
        have hxInt : (if decide (x = 1) then (1 : Int) else 0) = intFromBits x u8Ty := by
          rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> rfl
        rw [hxInt] at h8
        simp [evalValue, h8, evalUnOp, evalCastOp, bringInBounds_eq_intFromBits it hgood]
    | some srcIt =>
      simp only [hsrcIt] at hsrc
      obtain ⟨eo, heo, rfl⟩ := translateRvalue_cast_int htgt hsrc he
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

/-- `Machine::eval_statement` on an assignment to local `_i` whose source
evaluates to the value of a valid bit pattern `r` of `_i`'s type (`place_store`
stores at the local's declared type and ignores the type the source reports). -/
theorem evalStatement_assign_of {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (e : Gen.ValueExpr)
    (r : Nat) (hr : ValidBits (tyOf d) r) (T' : Gen.Type) (m1 : Mach)
    (hm1 : evalValue m e = .ok ((valOf (tyOf d) r, T'), m1))
    (h1 : FrameOk body f ctx locals m1 blk stmt) :
    ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
      FrameOk body f ctx (locals.set i (.init (.scalar ⟨r, (itOf d).size.bytes⟩))) m' blk stmt := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hT := h.decl_frag i d hd
  have hspec := (translateFn_spec body f h.hf).2.1 i d hd
  have hplace := evalPlace_local h.shape i hi _ hspec.2
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  have hL1 := h1.localAllocs_get i d slot hd hs
  have hst := typedStore_local_frag h1.shape i hT _ r hr hL1 (slotData_length _ _) ⟨1⟩
    (isAligned_one _)
  have hset := localAllocsFrom_set ctx 0 body.localDecls locals i d
    (.init (.scalar ⟨r, (itOf d).size.bytes⟩)) hd
  simp only [Nat.zero_add, slotData] at hset
  refine ⟨withMem m1 (ctx.base ++ localAllocs ctx body.localDecls
      (locals.set i (.init (.scalar ⟨r, (itOf d).size.bytes⟩))))
      ⟨.Store, .None, ctx.addrs.getD i 0, (itOf d).size⟩, ?_, ?_⟩
  · have hst' := hst
    simp only [localAllocs] at hst'
    rw [hset] at hst'
    simp [evalStatement, hplace, hm1, placeStore, hst', localAllocs]
  refine ⟨h.hf, withMem_shape h1.shape _, by simp [h.nlocals], ?_⟩
  · intro j d' slot' hd' hs'
    by_cases hij : i = j
    · subst hij
      rw [hd] at hd'; cases hd'
      simp [List.getElem?_set_self (by rw [h.nlocals]; exact hi)] at hs'
      subst hs'
      exact ⟨hT.tyBytes.symm, hr⟩
    · rw [List.getElem?_set_ne hij] at hs'
      exact h.slots j d' slot' hd' hs'

/-- `Machine::eval_statement` on a translated fragment assignment to an
integer local. -/
theorem evalStatement_assign {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (hint : intTypeOf d.ty = some (itOf d)) (rv : Rvalue)
    (hok : rvalueOk body.localDecls (itOf d) rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.localDecls rv = some e) :
    (∀ r, rvBits body.localDecls locals (itOf d) rv = some r →
      ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
        FrameOk body f ctx (locals.set i (.init (.scalar ⟨r, (itOf d).size.bytes⟩))) m' blk stmt) ∧
    (rvBits body.localDecls locals (itOf d) rv = none →
      ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood := h.decl_good i d hd
  have htyd : tyOf d = .Int (itOf d) := (tyOf_int hint).1
  have hspec := (translateFn_spec body f h.hf).2.1 i d hd
  have hplace := evalPlace_local h.shape i hi _ hspec.2
  obtain ⟨hrok, hrnone⟩ := evalValue_rvalue h (itOf d) hgood rv hok e he
  refine ⟨fun r hr => ?_, fun hnone => ?_⟩
  · obtain ⟨hrlt, m1, hm1, h1⟩ := hrok r hr
    exact evalStatement_assign_of h i d hd e r (by rw [htyd]; exact hrlt) _ m1
      (by rw [htyd]; exact hm1) h1
  · obtain ⟨msg, hmsg⟩ := hrnone hnone
    exact ⟨msg, by simp [evalStatement, hplace, hmsg]⟩

/-- `Machine::eval_statement` on a translated fragment `PlaceMention`. -/
theorem evalStatement_placeMention {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (hi : i < body.localDecls.length) :
    evalStatement m (.PlaceMention (.Local (localName i))) = .ok m := by
  obtain ⟨d, _, hd, _⟩ := h.slot_exists i hi
  have hspec := (translateFn_spec body f h.hf).2.1 i d hd
  have hplace := evalPlace_local h.shape i hi _ hspec.2
  simp [evalStatement, hplace]

/-! ## `bool` rvalues -/

/-- The outcome MiniRust's `BinOp::Rel` computes for two fragment values of
type `T`, given by their bit patterns: integers compare as mathematical
integers (`intCmp` of the decoded values) and `bool`s with `false < true`. -/
def cmpOf : Gen.Type → Nat → Nat → Ordering
  | .Int it, x, y => intCmp (intFromBits x it) (intFromBits y it)
  | .Bool, x, y => boolCmp (decide (x = 1)) (decide (y = 1))
  | _, _, _ => .eq

/-- The `bool` that `eval_rel_op` returns for a relational operator other than
`Cmp`. -/
def relBool : Gen.RelOp → Ordering → Bool
  | .Lt, o => o.isLT
  | .Gt, o => o.isGT
  | .Le, o => o.isLE
  | .Ge, o => o.isGE
  | .Eq, o => o.isEq
  | .Ne, o => o.isNe
  | .Cmp, _ => false

theorem translateRelOp_ne_cmp {op : MirAst.BinOp} {rel : Gen.RelOp}
    (h : translateRelOp op = some rel) : rel ≠ .Cmp := by
  cases op <;> simp [translateRelOp] at h <;> subst h <;> simp

theorem evalRelOp_bool (rel : Gen.RelOp) (hrel : rel ≠ .Cmp) (o : Ordering) :
    evalRelOp rel o = (.Bool (relBool rel o), .Bool) := by
  cases rel <;> simp_all [evalRelOp, relBool]

/-- `BinOp::Rel` on two fragment values of the same fragment type. -/
theorem evalBinOp_rel_frag {T : Gen.Type} {it : Gen.IntType} (hT : FragTy T it) (rel : Gen.RelOp)
    (hrel : rel ≠ .Cmp) (x y : Nat) :
    evalBinOp (.Rel rel) (valOf T x, T) (valOf T y, T) =
      .ok (.Bool (relBool rel (cmpOf T x y)), .Bool) := by
  cases hT <;> simp [evalBinOp, valOf, cmpOf, evalRelOp_bool rel hrel]

/-- `build::not` negates a `bool`: both of its transmutes succeed because
`1 - 0` and `1 - 1` are valid `bool` bytes. -/
theorem evalValue_boolNot (m m1 : Mach) (e : Gen.ValueExpr) (b : Bool)
    (he : evalValue m e = .ok ((.Bool b, .Bool), m1)) :
    evalValue m (boolNot e) = .ok ((.Bool (!b), .Bool), m1) := by
  have h8 := evalValue_boolToU8 m m1 e b he
  cases b <;> simp [boolNot, evalValue, h8, evalConstant, evalUnOp] <;> rfl

theorem translateRvalue_not_bool {decls : List LocalDecl} {op : Operand} {e : Gen.ValueExpr}
    (hok : operandOkB decls op = true) (he : translateRvalue decls (.unaryOp .not op) = some e) :
    ∃ eo, translateOperand op = some eo ∧ e = boolNot eo := by
  have hty : operandType decls op = some .Bool := by
    match op, hok with
    | .copy ⟨j, []⟩, hok =>
      simp only [operandOkB, Bool.and_eq_true, decide_eq_true_eq, operandIsBool_iff] at hok
      exact hok.2
    | .constant c, hok =>
      simp only [operandOkB, Bool.and_eq_true, operandIsBool_iff] at hok
      exact hok.1
  simp only [translateRvalue, Option.bind_eq_bind] at he
  cases heo : translateOperand op with
  | none => simp [heo] at he
  | some eo => simp [heo, hty] at he; exact ⟨eo, rfl, he.symm⟩

theorem translateRvalue_rel {decls : List LocalDecl} {op : MirAst.BinOp} {a b : Operand}
    {e : Gen.ValueExpr} {rel : Gen.RelOp} (hrel : translateRelOp op = some rel)
    (he : translateRvalue decls (.binaryOp op a b) = some e) :
    ∃ ea eb, translateOperand a = some ea ∧ translateOperand b = some eb ∧
      e = .BinOp (.Rel rel) ea eb := by
  simp only [translateRvalue, Option.bind_eq_bind] at he
  cases hea : translateOperand a with
  | none => simp [hea] at he
  | some ea =>
    cases heb : translateOperand b with
    | none => simp [hea, heb] at he
    | some eb => simp [hea, heb, hrel] at he; exact ⟨ea, eb, rfl, rfl, he.symm⟩

/-- The bit pattern an Anneal fragment rvalue of type `bool` evaluates to, or
`none` when evaluating it is UB. -/
def rvBitsB (decls : List LocalDecl) (locals : List LocalSlot) : Rvalue → Option Nat
  | .use op => opBits locals op
  | .unaryOp .not op => (opBits locals op).map (fun x => 1 - x)
  | .binaryOp op a b => do
    let rel ← translateRelOp op
    let T ← operandType decls a
    let x ← opBits locals a
    let y ← opBits locals b
    pure (if relBool rel (cmpOf T x y) then 1 else 0)
  | _ => none

/-- The operands of a fragment comparison have one fragment type. -/
theorem relOperandsOk_spec {decls : List LocalDecl} {a b : Operand}
    (h : relOperandsOk decls a b = true) :
    ∃ T it, FragTy T it ∧ operandType decls a = some T ∧ OperandOkT decls T a ∧
      OperandOkT decls T b := by
  unfold relOperandsOk at h
  split at h
  · next it hty =>
    simp only [Bool.and_eq_true] at h
    have hokT := operandOk_T h.1
    have hgood : GoodSize it.size.bytes := operandOk_good h.1
    exact ⟨.Int it, it, .int it hgood, hty, hokT, operandOk_T h.2⟩
  · next hty =>
    simp only [Bool.and_eq_true] at h
    exact ⟨.Bool, u8Ty, .bool, hty, operandOkB_T h.1, operandOkB_T h.2⟩
  · simp at h

/-- Evaluating a translated fragment rvalue of type `bool`. -/
theorem evalValue_rvalueB {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (rv : Rvalue) (hok : rvalueOkB body.localDecls rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.localDecls rv = some e) :
    (∀ r, rvBitsB body.localDecls locals rv = some r →
      r < 2 ∧
      ∃ m', evalValue m e = .ok ((valOf .Bool r, .Bool), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (rvBitsB body.localDecls locals rv = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  match rv, hok, he with
  | .use op, hok, he =>
    simp only [rvalueOkB] at hok
    simp only [translateRvalue] at he
    obtain ⟨hsome, hnone⟩ := evalValue_operandT h .bool op (operandOkB_T hok) e he
    refine ⟨fun r hr => ?_, fun hr => hnone hr⟩
    obtain ⟨hb, m', hm', h'⟩ := hsome r hr
    exact ⟨by simpa [ValidBits] using hb, m', hm', h'⟩
  | .unaryOp .not op, hok, he =>
    simp only [rvalueOkB] at hok
    obtain ⟨eo, heo, rfl⟩ := translateRvalue_not_bool hok he
    obtain ⟨hsome, hnone⟩ := evalValue_operandT h .bool op (operandOkB_T hok) eo heo
    cases hxo : opBits locals op with
    | none =>
      refine ⟨fun r hr => by simp [rvBitsB, hxo] at hr, fun _ => ?_⟩
      obtain ⟨msg, hmsg⟩ := hnone hxo
      exact ⟨msg, by simp [boolNot, boolToU8, evalValue, hmsg, evalConstant]⟩
    | some x =>
      obtain ⟨hx, m1, hm1, h1⟩ := hsome x hxo
      have hx2 : x < 2 := by simpa [ValidBits] using hx
      refine ⟨fun r hr => ?_, fun hr => by simp [rvBitsB, hxo] at hr⟩
      simp [rvBitsB, hxo] at hr
      subst hr
      refine ⟨by omega, m1, ?_, h1⟩
      rw [evalValue_boolNot m m1 eo _ hm1]
      rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> rfl
  | .unaryOp .neg _, hok, _ => simp [rvalueOkB] at hok
  | .unaryOp .ptrMetadata _, hok, _ => simp [rvalueOkB] at hok
  | .binaryOp op a b, hok, he =>
    simp only [rvalueOkB, Bool.and_eq_true] at hok
    obtain ⟨hrelSome, hops⟩ := hok
    obtain ⟨rel, hrel⟩ := Option.isSome_iff_exists.mp hrelSome
    obtain ⟨ea, eb, hea, heb, rfl⟩ := translateRvalue_rel hrel he
    obtain ⟨T, it, hT, htyA, hokA, hokB⟩ := relOperandsOk_spec hops
    obtain ⟨hasome, hanone⟩ := evalValue_operandT h hT a hokA ea hea
    cases hxa : opBits locals a with
    | none =>
      refine ⟨fun r hr => by simp [rvBitsB, hrel, htyA, hxa] at hr, fun _ => ?_⟩
      obtain ⟨msg, hmsg⟩ := hanone hxa
      exact ⟨msg, by simp [evalValue, hmsg]⟩
    | some x =>
      obtain ⟨_, m1, hm1, h1⟩ := hasome x hxa
      obtain ⟨hbsome, hbnone⟩ := evalValue_operandT h1 hT b hokB eb heb
      cases hyb : opBits locals b with
      | none =>
        refine ⟨fun r hr => by simp [rvBitsB, hrel, htyA, hxa, hyb] at hr, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hbnone hyb
        exact ⟨msg, by simp [evalValue, hm1, hmsg]⟩
      | some y =>
        obtain ⟨_, m2, hm2, h2⟩ := hbsome y hyb
        refine ⟨fun r hr => ?_, fun hr => by simp [rvBitsB, hrel, htyA, hxa, hyb] at hr⟩
        simp [rvBitsB, hrel, htyA, hxa, hyb] at hr
        subst hr
        refine ⟨by split <;> omega, m2, ?_, h2⟩
        simp only [evalValue, hm1, hm2, ok_bind, evalBinOp_rel_frag hT rel
          (translateRelOp_ne_cmp hrel) x y]
        cases relBool rel (cmpOf T x y) <;> rfl
  | .cast _ _ _, hok, _ => simp [rvalueOkB] at hok
  | .copyForDeref _, hok, _ => simp [rvalueOkB] at hok
  | .repeat _ _, hok, _ => simp [rvalueOkB] at hok
  | .ref _ _, hok, _ => simp [rvalueOkB] at hok
  | .rawPtr _ _, hok, _ => simp [rvalueOkB] at hok
  | .len _, hok, _ => simp [rvalueOkB] at hok
  | .discriminant _, hok, _ => simp [rvalueOkB] at hok
  | .aggregate _ _, hok, _ => simp [rvalueOkB] at hok
  | .threadLocalRef _, hok, _ => simp [rvalueOkB] at hok
  | .nullaryOp _ _, hok, _ => simp [rvalueOkB] at hok
  | .shallowInitBox _ _, hok, _ => simp [rvalueOkB] at hok
  | .wrapUnsafeBinder _ _, hok, _ => simp [rvalueOkB] at hok

/-- `Machine::eval_statement` on a translated fragment assignment to a `bool`
local. -/
theorem evalStatement_assignB {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (hbool : isBoolTy d.ty = true)
    (rv : Rvalue) (hok : rvalueOkB body.localDecls rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.localDecls rv = some e) :
    (∀ r, rvBitsB body.localDecls locals rv = some r →
      ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
        FrameOk body f ctx (locals.set i (.init (.scalar ⟨r, (itOf d).size.bytes⟩))) m' blk stmt) ∧
    (rvBitsB body.localDecls locals rv = none →
      ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have htyd : tyOf d = .Bool := (tyOf_bool hbool).1
  have hspec := (translateFn_spec body f h.hf).2.1 i d hd
  have hplace := evalPlace_local h.shape i hi _ hspec.2
  obtain ⟨hrok, hrnone⟩ := evalValue_rvalueB h rv hok e he
  refine ⟨fun r hr => ?_, fun hnone => ?_⟩
  · obtain ⟨hrlt, m1, hm1, h1⟩ := hrok r hr
    exact evalStatement_assign_of h i d hd e r (by rw [htyd]; exact hrlt) _ m1
      (by rw [htyd]; exact hm1) h1
  · obtain ⟨msg, hmsg⟩ := hrnone hnone
    exact ⟨msg, by simp [evalStatement, hplace, hmsg]⟩

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
    (hrest : ∀ e ∈ rest, e.1 ≠ localName i) {T : Gen.Type} {it : Gen.IntType} (hT : FragTy T it)
    (hty : mapGet fr.func.locals (localName i) = some T) (L' : List Gen.Allocation)
    (hmem : cm.memory.allocations = ctx.base ++ L') (a : Gen.Allocation) (ha : L'[i]? = some a)
    (hlive : a.live = true) (haddr : a.addr = ctx.addrs.getD i 0) (hkind : a.kind = .Stack)
    (hlen : a.data.length = it.size.bytes) (halign : a.align = ⟨it.size.bytes⟩) :
    storageDead fr cm (localName i) =
      .ok ({ fr with locals := ⟨rest⟩ },
           { cm with memory := { cm.memory with allocations := ctx.base ++ L'.set i (kill a) } }) := by
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp ha
  have hrest' : ∀ (x : Gen.LocalName) (y : Gen.ThinPointer (Gen.Memory.Provenance BM)),
      (x, y) ∈ rest → ¬x = localName i :=
    fun x y hxy => hrest (x, y) hxy
  simp [storageDead, mapIndex, hty, hT.layout, LayoutStrategy.expect_size,
    LayoutStrategy.expect_align, mapRemove, hloc, mapGet_cons, CM.deallocate,
    BM.deallocate, localPtr, listIndex, hmem, hi, hai, hlive, haddr, hkind, Allocation.size, hlen,
    halign, listSet, kill]
  exact hrest'

theorem deallocAll_callee (ctx : Ctx) (fuel : Nat) (fr : Frame) (cm : Gen.ConcurrentMemory BM)
    (is : List Nat) (L' : List Gen.Allocation) (hfuel : is.length ≤ fuel)
    (hloc : fr.locals = ⟨is.map (fun i => (localName i, localPtr ctx i))⟩) (hnodup : is.Nodup)
    (hmem : cm.memory.allocations = ctx.base ++ L')
    (hok : ∀ i ∈ is, ∃ T it a, mapGet fr.func.locals (localName i) = some T ∧
      FragTy T it ∧ L'[i]? = some a ∧ a.live = true ∧ a.addr = ctx.addrs.getD i 0 ∧
      a.kind = .Stack ∧ a.data.length = it.size.bytes ∧ a.align = ⟨it.size.bytes⟩) :
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
    obtain ⟨T, it, a, hty, hT, ha, hlive, haddr, hkind, hlen, halign⟩ := hok i (by simp)
    have hrest : ∀ e ∈ is.map (fun i => (localName i, localPtr ctx i)), e.1 ≠ localName i := by
      intro e he
      simp only [List.mem_map] at he
      obtain ⟨j, hj, rfl⟩ := he
      simp only [ne_eq, localName_inj]
      intro hji; subst hji; exact hni hj
    have hsd := storageDead_callee i _ (by simpa using hloc) hrest hT hty L' hmem a ha hlive
      haddr hkind hlen halign
    obtain ⟨cm', hcm', hcm'mem⟩ := ih fuel' { fr with locals := ⟨is.map (fun i => (localName i, localPtr ctx i))⟩ }
      { cm with memory := { cm.memory with allocations := ctx.base ++ L'.set i (kill a) } }
      (L'.set i (kill a)) (by simp at hfuel; omega) rfl hnd rfl
      (by
        intro j hj
        obtain ⟨T', it', a', hty', hT', ha', h1, h2, h3, h4, h5⟩ := hok j (by simp [hj])
        have hij : i ≠ j := fun h => hni (h ▸ hj)
        exact ⟨T', it', a', hty', hT', by rw [List.getElem?_set_ne hij]; exact ha', h1, h2, h3, h4,
          h5⟩)
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

theorem typedStore_base_bool {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (p : Ptr) (r : Nat) (a : Gen.Allocation)
    (hp : p.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a) (hlive : a.live = true)
    (haddr : a.addr = p.addr) (hlen : a.data.length = u8Ty.size.bytes) (b : Bool)
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    typedStore m p (.Bool b) .Bool align .None =
      .ok (withMem m (ctx.base.set r { a with data := scalarBytes u8Ty (if b then 1 else 0) } ++ L)
            ⟨.Store, .None, p.addr, u8Ty.size⟩) := by
  obtain ⟨hri, hai⟩ := List.getElem?_eq_some_iff.mp hr
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hck : checkValue (.Bool b) .Bool = .ok () := rfl
  have hblen : (scalarBytes u8Ty (if b then 1 else 0)).length = u8Ty.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hne : scalarBytes u8Ty (if b then 1 else 0) ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hblen, hu8]; omega)
  have hdrop : a.data.drop u8Ty.size.bytes = [] := List.drop_eq_nil_of_le (by omega)
  have hrlt : r < ctx.base.length + L.length := by omega
  simp only [typedStore, hck, encode_bool, CM.store, BM.store, hal, BM.check_ptr, hp,
    listIndex, h.allocs]
  simp [hne, hlive, haddr, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem,
    hdrop, List.set_append_left _ _ hri, hri, hrlt, hai]

/-- `typed_store` of the value of a valid bit pattern of a fragment type into
the caller's return place (an allocation in `base`). -/
theorem typedStore_base_frag {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (p : Ptr) (r : Nat) (a : Gen.Allocation)
    (hp : p.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a) (hlive : a.live = true)
    (haddr : a.addr = p.addr) {T : Gen.Type} {it : Gen.IntType} (hT : FragTy T it)
    (hlen : a.data.length = it.size.bytes) (bits : Nat) (hb : ValidBits T bits)
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    typedStore m p (valOf T bits) T align .None =
      .ok (withMem m (ctx.base.set r { a with data := scalarBytes it bits } ++ L)
            ⟨.Store, .None, p.addr, it.size⟩) := by
  cases hT with
  | int it hgood =>
    have hb' : bits < 2 ^ (8 * it.size.bytes) := hb
    have hst := typedStore_base h p r a hp hr hlive haddr it hgood hlen (intFromBits bits it)
      (canRepresent_intFromBits it bits hgood hb') align hal
    have hres : (intFromBits bits it % 2 ^ (8 * it.size.bytes)).toNat = bits := by
      rw [intFromBits_emod bits _ hb']; simp
    rw [hres] at hst
    exact hst
  | bool =>
    have hb' : bits < 2 := by simpa [ValidBits] using hb
    have hst := typedStore_base_bool h p r a hp hr hlive haddr hlen (decide (bits = 1)) align hal
    have hres : (if decide (bits = 1) then 1 else 0) = bits := by
      rcases (by omega : bits = 0 ∨ bits = 1) with rfl | rfl <;> rfl
    rw [hres] at hst
    exact hst

end MiniRustSpec.Correspondence
