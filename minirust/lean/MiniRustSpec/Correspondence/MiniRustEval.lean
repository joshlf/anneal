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

theorem intBoolTupleOf_good {t : MirAst.Ty} {it : Gen.IntType}
    (h : intBoolTupleOf t = some it) : GoodSize it.size.bytes := by
  unfold intBoolTupleOf at h
  revert h
  cases t.kind with
  | tuple ts =>
    cases ts with
    | nil => simp
    | cons t0 ts' =>
      cases ts' with
      | nil => simp
      | cons t1 ts'' =>
        cases ts'' with
        | cons _ _ => simp
        | nil =>
          cases t1 with
          | bool =>
            intro h
            cases hk : intTyBytes t0 with
            | none => simp [hk] at h
            | some p =>
              obtain ⟨s, n⟩ := p
              simp [hk] at h
              subst h
              exact intTyBytes_good hk
          | _ => simp
  | _ => simp

theorem GoodSize.pos {n : Nat} (h : GoodSize n) : 0 < n := by
  rcases h with h | h | h | h | h <;> omega

theorem align_eq (it : Gen.IntType) (h : GoodSize it.size.bytes) :
    IntType.align it = .ok ⟨it.size.bytes⟩ := by
  unfold IntType.align alignFromBytes
  rcases h with h | h | h | h | h <;> rw [h] <;> rfl

theorem layout_eq (it : Gen.IntType) (h : GoodSize it.size.bytes) :
    Type.layout (.Int it) = .ok (.Sized it.size ⟨it.size.bytes⟩) := by
  simp [Type.layout, align_eq it h]

theorem withOverflow_eq (it : Gen.IntType) (h : GoodSize it.size.bytes) :
    IntType.with_overflow it = .ok (intBoolTupleTy it) := by
  rcases h with h | h | h | h | h <;>
    cases it with | mk s sz => cases sz with | mk n =>
      simp at h; subst h; cases s <;> rfl

theorem head_size_and_align_tuple (it : Gen.IntType) (h : GoodSize it.size.bytes) :
    TupleHeadLayout.head_size_and_align
      ⟨⟨it.size.bytes + it.size.bytes⟩, ⟨it.size.bytes⟩, none⟩ =
      (⟨it.size.bytes + it.size.bytes⟩, ⟨it.size.bytes⟩) := by
  rcases h with h | h | h | h | h <;>
    cases it with | mk s sz => cases sz with | mk n =>
      simp at h; subst h; cases s <;> rfl

theorem layout_tuple (it : Gen.IntType) (h : GoodSize it.size.bytes) :
    Type.layout (intBoolTupleTy it) =
      .ok (.Sized ⟨it.size.bytes + it.size.bytes⟩ ⟨it.size.bytes⟩) := by
  simp [intBoolTupleTy, Type.layout, head_size_and_align_tuple it h]

/-! ## The callee's allocations and locals map -/

theorem scalarBytes_length (it : Gen.IntType) (bits : Nat) :
    (scalarBytes it bits).length = it.size.bytes := by
  simp [scalarBytes, leBytes_length]

theorem slotData_length (it : Gen.IntType) (slot : LocalSlot) :
    (slotData it slot).length = it.size.bytes := by
  unfold slotData
  split <;> simp [scalarBytes, uninitBytes, leBytes_length]

theorem tupleBytes_length (it : Gen.IntType) (bits b : Nat) (h : 0 < it.size.bytes) :
    (tupleBytes it bits b).length = it.size.bytes + it.size.bytes := by
  have hu8 : u8Ty.size.bytes = 1 := rfl
  simp only [tupleBytes, List.length_append, scalarBytes_length, hu8, List.length_replicate]
  omega

theorem tupleSlotData_length (it : Gen.IntType) (slot : LocalSlot) (h : 0 < it.size.bytes) :
    (tupleSlotData it slot).length = it.size.bytes + it.size.bytes := by
  unfold tupleSlotData
  split
  · exact tupleBytes_length it _ _ h
  · simp

theorem localAllocsFrom_getElem? (ctx : Ctx) (k : Nat) (ds : List LocalDecl) (slots : List LocalSlot)
    (j : Nat) (d : LocalDecl) (slot : LocalSlot) (hd : ds[j]? = some d) (hs : slots[j]? = some slot) :
    (localAllocsFrom ctx k ds slots)[j]? =
      some (localAlloc ctx (k + j) (itOf d) (declSlotData d slot)) := by
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
    (localAllocsFrom ctx k ds slots).set j (localAlloc ctx (k + j) (itOf d) (declSlotData d slot')) =
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

theorem checkValue_int {t : Gen.IntType} {i : Int} (h : IntType.can_represent t i = true) :
    checkValue (.Int i) (.Int t) = .ok () := by
  simp only [checkValue, ensureElseUb, h]; rfl

theorem checkValue_bool (b : Bool) : checkValue (.Bool b) .Bool = .ok () := rfl

/-- Encoding an in-window integer at an integer type yields the little-endian
bytes of its residue. -/
theorem encode_int (it : Gen.IntType) (v : Int) (hgood : GoodSize it.size.bytes)
    (hv : IntType.can_represent it v = true) :
    Type.encode (.Int it) (.Int v) = .ok (scalarBytes it (v % 2 ^ (8 * it.size.bytes)).toNat) := by
  obtain ⟨signed, size⟩ := it
  have h : inBounds v signed size = true := hv
  simp [Type.encode, Type.encodeInt, x86_64.ENDIANNESS, encode_eq signed size v h, scalarBytes,
    Size.bits]

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
    List.take_of_length_le, Type.decode, Type.decodeInt, mapM_data_scalarBytes, x86_64.ENDIANNESS,
    decode_leBytes signed size.bytes bits hb,
    checkValue_int (canRepresent_intFromBits ⟨signed, size⟩ bits hgood hb), withMem]

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
    List.take_of_length_le, Type.decode, Type.decodeInt, mapM_data_uninitBytes _ hpos, ub]

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
  have hck : checkValue (.Int v) (.Int it) = .ok () := checkValue_int hv
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
    List.take_of_length_le, decode_bool bits hb, checkValue_bool, withMem]

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

/-! ## `core::cmp::Ordering` locals

An `Ordering` local is stored like a `u8` local (`u8Ty`: one byte, alignment
one), and its byte must be a tag that `orderingTy`'s discriminator accepts:
`255` (`Less`, the `i8` `-1`), `0` (`Equal`), or `1` (`Greater`). The loads and
stores below are stated for any one-byte type `T` whose decoding, checking,
and encoding of the stored byte are known; for `orderingTy` these facts are
computed for each of the three tags. -/

theorem typedLoad_local_byte {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (T : Gen.Type) (bits : Nat) (v : Val)
    (hlay : Type.layout T = .ok (.Sized u8Ty.size ⟨u8Ty.size.bytes⟩))
    (hdec : Type.decode T (scalarBytes u8Ty bits) = .ok (some v)) (hck : checkValue v T = .ok ())
    (hL : L[i]? = some (localAlloc ctx i u8Ty (scalarBytes u8Ty bits)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) T align .None = .ok (v, m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hlen : (scalarBytes u8Ty bits).length = u8Ty.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD i 0, u8Ty.size⟩, ?_,
    withMem_shape h _⟩
  simp only [typedLoad, hlay, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [hu8, hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset,
    List.take_of_length_le, hdec, hck, withMem]

theorem typedLoad_local_byte_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (T : Gen.Type)
    (hlay : Type.layout T = .ok (.Sized u8Ty.size ⟨u8Ty.size.bytes⟩))
    (hdec : Type.decode T (uninitBytes u8Ty) = .ok none)
    (hL : L[i]? = some (localAlloc ctx i u8Ty (uninitBytes u8Ty)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) T align .None = .error (.ub msg) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hlen : (uninitBytes u8Ty).length = u8Ty.size.bytes := by simp [uninitBytes]
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨"load at type but the data in memory violates the language invariant", ?_⟩
  simp only [typedLoad, hlay, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [hu8, hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset,
    List.take_of_length_le, hdec, ub]

theorem typedStore_local_byte {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (T : Gen.Type) (data : List Byte) (v : Val)
    (bits : Nat) (hck : checkValue v T = .ok ())
    (henc : Type.encode T v = .ok (scalarBytes u8Ty bits))
    (hL : L[i]? = some (localAlloc ctx i u8Ty data)) (hlen : data.length = u8Ty.size.bytes)
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    typedStore m (localPtr ctx i) v T align .None =
      .ok (withMem m (ctx.base ++ L.set i (localAlloc ctx i u8Ty (scalarBytes u8Ty bits)))
            ⟨.Store, .None, ctx.addrs.getD i 0, u8Ty.size⟩) := by
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hblen : (scalarBytes u8Ty bits).length = u8Ty.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hne : scalarBytes u8Ty bits ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hblen, hu8]; omega)
  have hdrop : data.drop u8Ty.size.bytes = [] := List.drop_eq_nil_of_le (by omega)
  simp only [typedStore, hck, henc, CM.store, BM.store, hal, BM.check_ptr, localPtr,
    listIndex, h.allocs]
  simp [hne, hi, hLi, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem, hdrop]
  simp [localAlloc, hu8]

theorem layout_ordering : Type.layout orderingTy = .ok (.Sized u8Ty.size ⟨u8Ty.size.bytes⟩) := rfl

/-- `validBits` on every one-byte pattern: exactly the tags `255`, `0`, and
`1` decode at `orderingTy` (computed by the kernel). -/
theorem validBits_ordering_table :
    (List.range 256).all (fun b => validBits orderingTy b == (b == 255 || b == 0 || b == 1)) =
      true := by
  decide +kernel

/-- The bit patterns valid at `orderingTy` are its three tags. -/
theorem validBits_ordering (bits : Nat) :
    ValidBits orderingTy bits ↔ bits = 255 ∨ bits = 0 ∨ bits = 1 := by
  constructor
  · intro h
    have hlt : bits < 256 := by
      have := h.1
      simpa using this
    have hv : validBits orderingTy bits = true := (validBits_iff _ _).mpr h
    have ht := List.all_eq_true.mp validBits_ordering_table bits (List.mem_range.mpr hlt)
    rw [hv] at ht
    simpa [or_assoc] using ht
  · rintro (rfl | rfl | rfl) <;> exact (validBits_iff _ _).mp rfl

theorem decode_ordering_uninit : Type.decode orderingTy (uninitBytes u8Ty) = .ok none := rfl

/-! ## Fragment types

`FragTy T it` says that `T` is a fragment type stored like the integer type
`it`: an integer type of good size is stored as itself, and `bool` and
`core::cmp::Ordering` (`orderingTy`) as `u8`. -/

/-- Fragment types and their storage integer types. -/
inductive FragTy : Gen.Type → Gen.IntType → Prop
  | int (it : Gen.IntType) (h : GoodSize it.size.bytes) : FragTy (.Int it) it
  | bool : FragTy .Bool u8Ty
  | ordering : FragTy orderingTy u8Ty

/-- The fragment types that MiniRust's `BinOp::Rel` compares: integers (by
value) and `bool` (`false < true`); an `Ordering` value is not comparable. -/
inductive RelTy : Gen.Type → Gen.IntType → Prop
  | int (it : Gen.IntType) (h : GoodSize it.size.bytes) : RelTy (.Int it) it
  | bool : RelTy .Bool u8Ty

theorem RelTy.frag {T : Gen.Type} {it : Gen.IntType} (h : RelTy T it) : FragTy T it := by
  cases h with
  | int it h => exact .int it h
  | bool => exact .bool

/-- The MiniRust value that the bit pattern `bits` encodes at fragment type
`T`; for an enum, the value that its little-endian bytes decode to. -/
def valOf : Gen.Type → Nat → Val
  | .Int it, bits => .Int (intFromBits bits it)
  | .Bool, bits => .Bool (decide (bits = 1))
  | T@(.Enum _ _ _ size _), bits =>
    match Type.decode T (scalarBytes ⟨.Unsigned, size⟩ bits) with
    | .ok (some v) => v
    | _ => .Int 0
  | _, _ => .Int 0

theorem decode_ordering {bits : Nat} (hb : ValidBits orderingTy bits) :
    Type.decode orderingTy (scalarBytes u8Ty bits) = .ok (some (valOf orderingTy bits)) := by
  rcases (validBits_ordering bits).mp hb with rfl | rfl | rfl <;> rfl

theorem checkValue_ordering {bits : Nat} (hb : ValidBits orderingTy bits) :
    checkValue (valOf orderingTy bits) orderingTy = .ok () := by
  rcases (validBits_ordering bits).mp hb with rfl | rfl | rfl <;> rfl

theorem encode_ordering {bits : Nat} (hb : ValidBits orderingTy bits) :
    Type.encode orderingTy (valOf orderingTy bits) = .ok (scalarBytes u8Ty bits) := by
  rcases (validBits_ordering bits).mp hb with rfl | rfl | rfl <;> rfl

theorem FragTy.good {T : Gen.Type} {it : Gen.IntType} (h : FragTy T it) : GoodSize it.size.bytes := by
  cases h with
  | int _ h => exact h
  | bool => simp [u8Ty, GoodSize]
  | ordering => simp [u8Ty, GoodSize]

theorem FragTy.layout {T : Gen.Type} {it : Gen.IntType} (h : FragTy T it) :
    Type.layout T = .ok (.Sized it.size ⟨it.size.bytes⟩) := by
  cases h with
  | int _ h => exact layout_eq _ h
  | bool => exact layout_bool
  | ordering => exact layout_ordering

theorem FragTy.tyBytes {T : Gen.Type} {it : Gen.IntType} (h : FragTy T it) :
    tyBytes T = it.size.bytes := by
  cases h <;> rfl

theorem FragTy.validBits_lt {T : Gen.Type} {it : Gen.IntType} (h : FragTy T it) {bits : Nat}
    (hb : ValidBits T bits) : bits < 2 ^ (8 * it.size.bytes) := by
  cases h with
  | int _ _ => exact hb
  | bool => simp [ValidBits] at hb; simp [u8Ty]; omega
  | ordering =>
    rcases (validBits_ordering bits).mp hb with rfl | rfl | rfl <;> simp [u8Ty]

theorem FragTy.not_tuple {d : LocalDecl} (h : FragTy (tyOf d) (itOf d)) :
    intBoolTupleOf d.ty = none := by
  cases ht : intBoolTupleOf d.ty with
  | none => rfl
  | some it =>
    obtain ⟨h1, _⟩ := tyOf_tuple ht
    rw [h1] at h
    cases h

theorem FragTy.declSlotData {d : LocalDecl} (h : FragTy (tyOf d) (itOf d)) (slot : LocalSlot) :
    declSlotData d slot = slotData (itOf d) slot :=
  declSlotData_of_none h.not_tuple slot

theorem FragTy.unique {T : Gen.Type} {it it' : Gen.IntType} (h : FragTy T it) (h' : FragTy T it') :
    it = it' := by
  cases h <;> cases h' <;> rfl

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
  | ordering =>
    exact typedLoad_local_byte h i orderingTy bits _ layout_ordering (decode_ordering hb)
      (checkValue_ordering hb) hL align hal

theorem typedLoad_local_frag_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) {T : Gen.Type}
    {it : Gen.IntType} (hT : FragTy T it) (hL : L[i]? = some (localAlloc ctx i it (uninitBytes it)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) T align .None = .error (.ub msg) := by
  cases hT with
  | int it hgood => exact typedLoad_local_uninit h i it hgood hL align hal
  | bool => exact typedLoad_local_bool_uninit h i hL align hal
  | ordering =>
    exact typedLoad_local_byte_uninit h i orderingTy layout_ordering decode_ordering_uninit hL
      align hal

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
  | ordering =>
    exact typedStore_local_byte h i orderingTy data _ bits (checkValue_ordering hb)
      (encode_ordering hb) hL hlen align hal

/-- All fragment local types (both scalar `FragTy` and 2-tuples `intBoolTupleTy it`)
and their alignment storage integer types. -/
inductive LocalTy : Gen.Type → Gen.IntType → Prop
  | frag {T : Gen.Type} {it : Gen.IntType} (h : FragTy T it) : LocalTy T it
  | tuple (it : Gen.IntType) (h : GoodSize it.size.bytes) : LocalTy (intBoolTupleTy it) it

theorem LocalTy.good {T : Gen.Type} {it : Gen.IntType} (h : LocalTy T it) :
    GoodSize it.size.bytes := by
  cases h with
  | frag hf => exact hf.good
  | tuple _ hg => exact hg

theorem LocalTy.layout {T : Gen.Type} {it : Gen.IntType} (h : LocalTy T it) :
    Type.layout T = .ok (.Sized ⟨tyBytes T⟩ ⟨it.size.bytes⟩) := by
  cases h with
  | frag hf => rw [hf.tyBytes]; exact hf.layout
  | tuple it hg => exact layout_tuple it hg

/-- Storage integer type associated with a `LocalTy` type `T`. -/
def storageIt : Gen.Type → Gen.IntType
  | .Int it => it
  | .Tuple ((_, .Int it) :: _) _ _ => it
  | _ => u8Ty

theorem LocalTy.storageIt_eq {T : Gen.Type} {it : Gen.IntType} (h : LocalTy T it) :
    storageIt T = it := by
  cases h with
  | frag hf => cases hf <;> rfl
  | tuple _ _ => rfl

theorem LocalTy.unique {T : Gen.Type} {it it' : Gen.IntType} (h : LocalTy T it)
    (h' : LocalTy T it') : it = it' := by
  rw [← h.storageIt_eq, h'.storageIt_eq]

theorem LocalTy.of_validBits {T : Gen.Type} {it : Gen.IntType} (h : LocalTy T it) {bits : Nat}
    (hb : ValidBits T bits) : FragTy T it := by
  cases h with
  | frag hf => exact hf
  | tuple _ _ => simp [intBoolTupleTy, ValidBits] at hb

/-- A fragment local's declared MiniRust type is a `LocalTy` aligned like
`itOf d`. -/
theorem localTy_of_decl {d : LocalDecl} (h : scalarTypeOf d.ty = some (tyOf d)) :
    LocalTy (tyOf d) (itOf d) := by
  rcases scalarTypeOf_cases h with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
  · obtain ⟨h1, h2⟩ := tyOf_bool hb; rw [h1, h2]; exact .frag .bool
  · obtain ⟨h1, h2⟩ := tyOf_int hit; rw [h1, h2]; exact .frag (.int it (intTypeOf_good hit))
  · obtain ⟨h1, h2⟩ := tyOf_ordering ho; rw [h1, h2]; exact .frag .ordering
  · obtain ⟨h1, h2⟩ := tyOf_tuple ht; rw [h1, h2]; exact .tuple it (intBoolTupleOf_good ht)

theorem declSlotData_length {d : LocalDecl} (hd : scalarTypeOf d.ty = some (tyOf d))
    (slot : LocalSlot) : (declSlotData d slot).length = tyBytes (tyOf d) := by
  rcases scalarTypeOf_cases hd with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
  · obtain ⟨h1, h2⟩ := tyOf_bool hb
    have hf : FragTy (tyOf d) (itOf d) := by rw [h1, h2]; exact .bool
    rw [hf.declSlotData, slotData_length, hf.tyBytes]
  · obtain ⟨h1, h2⟩ := tyOf_int hit
    have hf : FragTy (tyOf d) (itOf d) := by rw [h1, h2]; exact .int it (intTypeOf_good hit)
    rw [hf.declSlotData, slotData_length, hf.tyBytes]
  · obtain ⟨h1, h2⟩ := tyOf_ordering ho
    have hf : FragTy (tyOf d) (itOf d) := by rw [h1, h2]; exact .ordering
    rw [hf.declSlotData, slotData_length, hf.tyBytes]
  · obtain ⟨h1, _⟩ := tyOf_tuple ht
    rw [declSlotData_of_some ht, h1, tupleSlotData_length it slot (intBoolTupleOf_good ht).pos]
    rfl

/-! ## `(Int, bool)` 2-tuple locals -/

/-- MiniRust `Value::Tuple` corresponding to bit patterns `(bits, b)` at
`intBoolTupleTy it`. -/
def tupleVal (it : Gen.IntType) (bits b : Nat) : Val :=
  .Tuple [.Int (intFromBits bits it), .Bool (decide (b = 1))]

theorem checkValue_tuple (it : Gen.IntType) (bits b : Nat) (hgood : GoodSize it.size.bytes)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) :
    checkValue (tupleVal it bits b) (intBoolTupleTy it) = .ok () := by
  simp [tupleVal, intBoolTupleTy, checkValue, ensureElseUb, checkFields,
    canRepresent_intFromBits it bits hgood hbits]

theorem encode_tuple (it : Gen.IntType) (bits b : Nat) (hgood : GoodSize it.size.bytes)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) (hb : b < 2) :
    Type.encode (intBoolTupleTy it) (tupleVal it bits b) = .ok (tupleBytes it bits b) := by
  have hpos := hgood.pos
  have henc0 : Type.encodeInt it (.Int (intFromBits bits it)) = .ok (scalarBytes it bits) := by
    have h := encode_int it (intFromBits bits it) hgood (canRepresent_intFromBits it bits hgood hbits)
    have hres0 : (intFromBits bits it % 2 ^ (8 * it.size.bytes)).toNat = bits := by
      rw [intFromBits_emod bits _ hbits]; simp
    rw [hres0] at h
    exact h
  have hb_eq : [Gen.AbstractByte.Init (if b = 1 then 1 else 0) none] = scalarBytes u8Ty b := by
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> rfl
  have hlen0 := scalarBytes_length it bits
  have hlen1 : (scalarBytes u8Ty b).length = 1 := scalarBytes_length u8Ty b
  have hle0 : (it.size.bytes : Int) ≤ (it.size.bytes : Int) + it.size.bytes := by omega
  have hle1 : (it.size.bytes : Int) + 1 ≤ (it.size.bytes : Int) + it.size.bytes := by omega
  have htk : (scalarBytes it bits ++ List.replicate it.size.bytes Gen.AbstractByte.Uninit).take it.size.bytes =
      scalarBytes it bits := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hdr : (scalarBytes it bits ++ List.replicate it.size.bytes Gen.AbstractByte.Uninit).drop (it.size.bytes + 1) =
      List.replicate (it.size.bytes - 1) Gen.AbstractByte.Uninit := by
    rw [List.drop_append, hlen0, List.drop_eq_nil_of_le (by omega), List.nil_append, List.drop_replicate]
    congr 1; omega
  simp [intBoolTupleTy, tupleVal, Type.encode, Type.encodeFields, head_size_and_align_tuple it hgood,
    henc0, hb_eq, writeSubsliceAtIndex, hlen0, hlen1, hle0, hle1, List.drop_replicate, htk, hdr,
    tupleBytes, List.append_assoc]

theorem decode_int_scalarBytes (it : Gen.IntType) (bits : Nat)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) :
    Type.decode (.Int it) (scalarBytes it bits) = .ok (some (.Int (intFromBits bits it))) := by
  obtain ⟨signed, size⟩ := it
  have hlen : (scalarBytes ⟨signed, size⟩ bits).length = size.bytes := by
    simp [scalarBytes, leBytes_length]
  simp [Type.decode, Type.decodeInt, hlen, mapM_data_scalarBytes, x86_64.ENDIANNESS,
    decode_leBytes signed size.bytes bits hbits]

theorem decode_int_uninitBytes (it : Gen.IntType) (hgood : GoodSize it.size.bytes) :
    Type.decode (.Int it) (uninitBytes it) = .ok none := by
  have hpos := hgood.pos
  obtain ⟨signed, size⟩ := it
  have hlen : (uninitBytes ⟨signed, size⟩).length = size.bytes := by simp [uninitBytes]
  simp [Type.decode, Type.decodeInt, hlen, mapM_data_uninitBytes _ hpos]

theorem take_tupleBytes_field0 (it : Gen.IntType) (bits b : Nat) :
    (tupleBytes it bits b).take it.size.bytes = scalarBytes it bits := by
  have hlen0 := scalarBytes_length it bits
  rw [tupleBytes, List.append_assoc, List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega)]

theorem drop_take_tupleBytes_field1 (it : Gen.IntType) (bits b : Nat) :
    ((tupleBytes it bits b).drop it.size.bytes).take 1 = scalarBytes u8Ty b := by
  have hlen0 := scalarBytes_length it bits
  have hlen1 : (scalarBytes u8Ty b).length = 1 := scalarBytes_length u8Ty b
  rw [tupleBytes, List.append_assoc, List.drop_append_of_le_length (by omega),
    List.drop_eq_nil_of_le (by omega), List.nil_append, List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega)]

theorem decode_tuple (it : Gen.IntType) (bits b : Nat) (hgood : GoodSize it.size.bytes)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) (hb : b < 2) :
    Type.decode (intBoolTupleTy it) (tupleBytes it bits b) = .ok (some (tupleVal it bits b)) := by
  have hpos := hgood.pos
  have hpos1 : 1 ≤ it.size.bytes := hpos
  have hlen := tupleBytes_length it bits b hpos
  have ht0 := take_tupleBytes_field0 it bits b
  have ht1 := drop_take_tupleBytes_field1 it bits b
  have hle0 : (it.size.bytes : Int) ≤ (it.size.bytes : Int) + it.size.bytes := by omega
  have hu8 : u8Ty.size.bytes = 1 := rfl
  rw [intBoolTupleTy, Type.decode]
  simp [Type.decodeFields, head_size_and_align_tuple it hgood,
    hlen, layout_eq it hgood, layout_bool, LayoutStrategy.expect_size, subsliceWithLength,
    hle0, hu8, hpos1, ht0, ht1, decode_int_scalarBytes it bits hbits, decode_bool b hb, tupleVal]

theorem decode_tuple_uninit (it : Gen.IntType) (hgood : GoodSize it.size.bytes) :
    Type.decode (intBoolTupleTy it) (List.replicate (it.size.bytes + it.size.bytes) .Uninit) =
      .ok none := by
  have hpos := hgood.pos
  have hmin : min it.size.bytes (it.size.bytes + it.size.bytes) = it.size.bytes :=
    Nat.min_eq_left (by omega)
  have hle0 : (it.size.bytes : Int) ≤ (it.size.bytes : Int) + it.size.bytes := by omega
  have hdec0 := decode_int_uninitBytes it hgood
  rw [uninitBytes] at hdec0
  rw [intBoolTupleTy, Type.decode]
  simp [Type.decodeFields, head_size_and_align_tuple it hgood,
    layout_eq it hgood, LayoutStrategy.expect_size, subsliceWithLength, hle0, hmin, hdec0]

theorem typedLoad_local_tuple {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes) (bits b : Nat) (hbits : bits < 2 ^ (8 * it.size.bytes))
    (hb : b < 2) (hL : L[i]? = some (localAlloc ctx i it (tupleBytes it bits b)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) (intBoolTupleTy it) align .None =
        .ok (tupleVal it bits b, m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hlen := tupleBytes_length it bits b hpos
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨withMem m (ctx.base ++ L)
      ⟨.Load, .None, ctx.addrs.getD i 0, ⟨it.size.bytes + it.size.bytes⟩⟩, ?_, withMem_shape h _⟩
  simp only [typedLoad, layout_tuple it hgood, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [Nat.ne_of_gt hpos, hi, hLi, Allocation.size, hlen, listSet, subsliceWithLength, hset,
    List.take_of_length_le, decode_tuple it bits b hgood hbits hb,
    checkValue_tuple it bits b hgood hbits, withMem]

theorem typedLoad_local_tuple_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes)
    (hL : L[i]? = some (localAlloc ctx i it (List.replicate (it.size.bytes + it.size.bytes) .Uninit)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) (intBoolTupleTy it) align .None = .error (.ub msg) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hset := set_self_of_getElem? L i _ hL
  refine ⟨"load at type but the data in memory violates the language invariant", ?_⟩
  simp only [typedLoad, layout_tuple it hgood, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [Nat.ne_of_gt hpos, hi, hLi, Allocation.size, listSet, subsliceWithLength, hset,
    List.take_of_length_le, decode_tuple_uninit it hgood, ub]

theorem typedStore_local_tuple {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes) (data : List Byte) (bits b : Nat)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) (hb : b < 2)
    (hL : L[i]? = some (localAlloc ctx i it data)) (hlen : data.length = it.size.bytes + it.size.bytes)
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    typedStore m (localPtr ctx i) (tupleVal it bits b) (intBoolTupleTy it) align .None =
      .ok (withMem m (ctx.base ++ L.set i (localAlloc ctx i it (tupleBytes it bits b)))
            ⟨.Store, .None, ctx.addrs.getD i 0, ⟨it.size.bytes + it.size.bytes⟩⟩) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hblen := tupleBytes_length it bits b hpos
  have hck := checkValue_tuple it bits b hgood hbits
  have henc := encode_tuple it bits b hgood hbits hb
  have hne : tupleBytes it bits b ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hdrop : data.drop (it.size.bytes + it.size.bytes) = [] := List.drop_eq_nil_of_le (by omega)
  simp only [typedStore, hck, henc, CM.store, BM.store, hal, BM.check_ptr, localPtr,
    listIndex, h.allocs]
  simp [hne, hi, hLi, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem, hdrop,
    localAlloc]

/-- MiniRust `Value` corresponding to an Anneal `Value` of fragment local type `T`. -/
def valOfValue (T : Gen.Type) : Value → Val
  | .scalar sc => valOf T sc.bits
  | .aggregate 0 [.scalar sc0, .scalar sc1] =>
    match tupleIntOfTy T with
    | some it => tupleVal it sc0.bits sc1.bits
    | none => .Int 0
  | _ => .Int 0

theorem typedLoad_local_localTy {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (d : LocalDecl)
    (hd : scalarTypeOf d.ty = some (tyOf d)) (v : Value) (hv : SlotOk (tyOf d) (.init v))
    (hL : L[i]? = some (localAlloc ctx i (itOf d) (declSlotData d (.init v))))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) (tyOf d) align .None = .ok (valOfValue (tyOf d) v, m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  rcases scalarTypeOf_cases hd with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
  · obtain ⟨h1, h2⟩ := tyOf_bool hb
    have hf : FragTy (tyOf d) (itOf d) := by rw [h1, h2]; exact .bool
    rw [hf.declSlotData] at hL
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      exact typedLoad_local_frag h i hf sc.bits hvb hL align hal
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨_, hty, _⟩ =>
      rw [h1] at hty; simp at hty
  · obtain ⟨h1, h2⟩ := tyOf_int hit
    have hf : FragTy (tyOf d) (itOf d) := by rw [h1, h2]; exact .int it (intTypeOf_good hit)
    rw [hf.declSlotData] at hL
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      exact typedLoad_local_frag h i hf sc.bits hvb hL align hal
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨_, hty, _⟩ =>
      rw [h1] at hty; simp at hty
  · obtain ⟨h1, h2⟩ := tyOf_ordering ho
    have hf : FragTy (tyOf d) (itOf d) := by rw [h1, h2]; exact .ordering
    rw [hf.declSlotData] at hL
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      exact typedLoad_local_frag h i hf sc.bits hvb hL align hal
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨_, hty, _⟩ =>
      rw [h1] at hty; simp at hty
  · obtain ⟨h1, h2⟩ := tyOf_tuple ht
    rw [declSlotData_of_some ht] at hL
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      rw [h1] at hvb; simp [intBoolTupleTy, ValidBits] at hvb
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨it'', hty, _, hb0, _, hb1⟩ =>
      rw [h1, tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at hty
      subst hty
      rw [h2] at hL
      rw [h1]
      simpa [valOfValue, tupleSlotData] using typedLoad_local_tuple h i it (intBoolTupleOf_good ht)
        sc0.bits sc1.bits hb0 hb1 hL align hal

theorem typedLoad_local_localTy_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (d : LocalDecl)
    (hd : scalarTypeOf d.ty = some (tyOf d))
    (hL : L[i]? = some (localAlloc ctx i (itOf d) (declSlotData d .uninit)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) (tyOf d) align .None = .error (.ub msg) := by
  rcases scalarTypeOf_cases hd with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
  · obtain ⟨h1, h2⟩ := tyOf_bool hb
    have hfrag : FragTy (tyOf d) (itOf d) := by rw [h1, h2]; exact .bool
    rw [hfrag.declSlotData] at hL
    exact typedLoad_local_frag_uninit h i hfrag hL align hal
  · obtain ⟨h1, h2⟩ := tyOf_int hit
    have hfrag : FragTy (tyOf d) (itOf d) := by rw [h1, h2]; exact .int it (intTypeOf_good hit)
    rw [hfrag.declSlotData] at hL
    exact typedLoad_local_frag_uninit h i hfrag hL align hal
  · obtain ⟨h1, h2⟩ := tyOf_ordering ho
    have hfrag : FragTy (tyOf d) (itOf d) := by rw [h1, h2]; exact .ordering
    rw [hfrag.declSlotData] at hL
    exact typedLoad_local_frag_uninit h i hfrag hL align hal
  · obtain ⟨h1, h2⟩ := tyOf_tuple ht
    rw [declSlotData_of_some ht, h2] at hL
    simp only [tupleSlotData] at hL
    rw [h1]
    exact typedLoad_local_tuple_uninit h i it (intBoolTupleOf_good ht) hL align hal

/-! ## Places of the callee's locals -/

theorem evalPlace_local {m : Mach} {ctx : Ctx} {f : Gen.Function} {n blk stmt : Nat}
    {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrame f ctx n blk stmt] allocs) (i : Nat) (hi : i < n)
    (T : Gen.Type) (hT : mapGet f.locals (localName i) = some T) :
    evalPlace m (.Local (localName i)) =
      .ok ({ ptr := { thin_pointer := localPtr ctx i, metadata := none }, aligned := true }, T) := by
  simp [evalPlace, curFrame_eq h, mapIndex, calleeFrame, hT, mapGet_localsMap ctx n i hi,
    ThinPointer.widen]

/-- Pointer to field 1 (offset `it.size.bytes`) of an `(it, bool)` tuple local `_i`. -/
def localField1Ptr (ctx : Ctx) (i : Nat) (it : Gen.IntType) : Ptr :=
  { addr := ctx.addrs.getD i 0 + it.size.bytes,
    provenance := some (⟨((ctx.base.length + i : Nat) : Int)⟩, ()) }

theorem wrapping_offset_localPtr (ctx : Ctx) (i : Nat) (it : Gen.IntType)
    (h0 : 0 ≤ ctx.addrs.getD i 0) (hlt : ctx.addrs.getD i 0 + (it.size.bytes : Int) < 2 ^ 64) :
    ThinPointer.wrapping_offset (localPtr ctx i) (it.size.bytes : Int) = localField1Ptr ctx i it := by
  have hb : (2 : Int) ^ Size.bits x86_64.PTR_SIZE = 2 ^ 64 := rfl
  have hnonneg : 0 ≤ ctx.addrs.getD i 0 + (it.size.bytes : Int) := by omega
  simp only [ThinPointer.wrapping_offset, localPtr, localField1Ptr, bringInBounds, hb]
  rw [Int.emod_eq_of_lt hnonneg hlt]

theorem inBounds_unsigned_ptrSize (addr : Int) (h0 : 0 ≤ addr) (hlt : addr < 2 ^ 64) :
    inBounds addr .Unsigned x86_64.PTR_SIZE = true := by
  have hb : (2 : Int) ^ Size.bits x86_64.PTR_SIZE = 2 ^ 64 := rfl
  simp only [inBounds, hb, decide_eq_true_eq, Bool.and_eq_true]
  exact ⟨h0, hlt⟩

theorem inBounds_goodSize_ptrSize (it : Gen.IntType) (hgood : GoodSize it.size.bytes) :
    inBounds (it.size.bytes : Int) .Signed x86_64.PTR_SIZE = true := by
  rcases hgood with h | h | h | h | h <;> rw [h] <;> decide

theorem evalPlace_field0 {m : Mach} {ctx : Ctx} {f : Gen.Function} {n blk stmt : Nat}
    {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrame f ctx n blk stmt] allocs) (i : Nat) (hi : i < n)
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (hT : mapGet f.locals (localName i) = some (intBoolTupleTy it))
    (haddr : AddrOk (ctx.addrs.getD i 0) it) :
    evalPlace m (.Field (.Local (localName i)) 0) =
      .ok ({ ptr := { thin_pointer := localPtr ctx i, metadata := none }, aligned := true }, .Int it) := by
  have hpos := hgood.pos
  have hloc := evalPlace_local h i hi (intBoolTupleTy it) hT
  have hin0 : inBounds (0 : Int) .Signed x86_64.PTR_SIZE = true := by decide
  have hinAddr : inBounds (ctx.addrs[i]?.getD 0) .Unsigned x86_64.PTR_SIZE = true :=
    inBounds_unsigned_ptrSize _ haddr.2.1 (by have := haddr.2.2; simp only [List.getD_eq_getElem?_getD] at this; omega)
  have hptr : ptrOffsetInbounds m (localPtr ctx i) 0 = .ok (localPtr ctx i) := by
    simp [ptrOffsetInbounds, CM.signed_dereferenceable, BM.signed_dereferenceable,
      BM.dereferenceable, BM.check_ptr, hin0, localPtr, hinAddr]
  rw [evalPlace]
  simp [hloc, intBoolTupleTy, listIndex, Type.layout, head_size_and_align_tuple it hgood,
    computeSize, LayoutStrategy.compute_size_and_align, hptr, align_eq it hgood,
    LayoutStrategy.is_sized, ThinPointer.widen]

theorem evalPlace_field1 {m : Mach} {ctx : Ctx} {f : Gen.Function} {n blk stmt : Nat}
    {L : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrame f ctx n blk stmt] (ctx.base ++ L))
    (i : Nat) (hi : i < n) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (hT : mapGet f.locals (localName i) = some (intBoolTupleTy it))
    (data : List Byte) (hL : L[i]? = some (localAlloc ctx i it data))
    (hlen : data.length = it.size.bytes + it.size.bytes)
    (haddr : AddrOk (ctx.addrs.getD i 0) it) :
    evalPlace m (.Field (.Local (localName i)) 1) =
      .ok ({ ptr := { thin_pointer := localField1Ptr ctx i it, metadata := none }, aligned := true }, .Bool) := by
  have hpos := hgood.pos
  obtain ⟨hiL, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hloc := evalPlace_local h i hi (intBoolTupleTy it) hT
  have hbounds : ¬ ((it.size.bytes : Int) + it.size.bytes < it.size.bytes) := by omega
  have hinAddr : inBounds (ctx.addrs[i]?.getD 0 + (it.size.bytes : Int)) .Unsigned x86_64.PTR_SIZE = true :=
    inBounds_unsigned_ptrSize _ (by have := haddr.2.1; simp only [List.getD_eq_getElem?_getD] at this; omega) haddr.2.2
  have hptr : ptrOffsetInbounds m (localPtr ctx i) (it.size.bytes : Int) =
      .ok (localField1Ptr ctx i it) := by
    simp only [ptrOffsetInbounds, CM.signed_dereferenceable, BM.signed_dereferenceable,
      Int.toNat_natCast, BM.dereferenceable]
    simp [Nat.ne_of_gt hpos, BM.check_ptr, localPtr, localField1Ptr, listIndex, h.allocs, hiL, hLi,
      Allocation.size, hlen, hbounds, inBounds_goodSize_ptrSize it hgood, hinAddr]
  have hnotlt : ¬ (it.size.bytes + it.size.bytes < it.size.bytes) := by omega
  rw [evalPlace]
  simp [hloc, intBoolTupleTy, listIndex, Type.layout, head_size_and_align_tuple it hgood,
    computeSize, LayoutStrategy.compute_size_and_align, hnotlt, hptr,
    LayoutStrategy.is_sized, ThinPointer.widen]

theorem typedLoad_local_tuple_field0 {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes) (bits b : Nat) (hbits : bits < 2 ^ (8 * it.size.bytes))
    (hL : L[i]? = some (localAlloc ctx i it (tupleBytes it bits b)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ m', typedLoad m (localPtr ctx i) (.Int it) align .None =
        .ok (.Int (intFromBits bits it), m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hlen := tupleBytes_length it bits b hpos
  have hset := set_self_of_getElem? L i _ hL
  have ht0 := take_tupleBytes_field0 it bits b
  have hbounds : ¬ ((it.size.bytes : Int) + it.size.bytes < it.size.bytes) := by omega
  refine ⟨withMem m (ctx.base ++ L) ⟨.Load, .None, ctx.addrs.getD i 0, it.size⟩, ?_,
    withMem_shape h _⟩
  simp only [typedLoad, layout_eq _ hgood, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [Nat.ne_of_gt hpos, hi, hLi, Allocation.size, hlen, hbounds, listSet,
    subsliceWithLength, hset, ht0, decode_int_scalarBytes it bits hbits,
    checkValue_int (canRepresent_intFromBits it bits hgood hbits), withMem]

theorem typedLoad_local_tuple_field0_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes)
    (hL : L[i]? = some (localAlloc ctx i it (List.replicate (it.size.bytes + it.size.bytes) .Uninit)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0) = true) :
    ∃ msg, typedLoad m (localPtr ctx i) (.Int it) align .None = .error (.ub msg) := by
  have hpos := hgood.pos
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hset := set_self_of_getElem? L i _ hL
  have hmin : min it.size.bytes (it.size.bytes + it.size.bytes) = it.size.bytes :=
    Nat.min_eq_left (by omega)
  have htk0 : (List.replicate (it.size.bytes + it.size.bytes) Gen.AbstractByte.Uninit).take it.size.bytes =
      uninitBytes it := by
    simp [uninitBytes, List.take_replicate, hmin]
  have hbounds : ¬ ((it.size.bytes : Int) + it.size.bytes < it.size.bytes) := by omega
  refine ⟨"load at type but the data in memory violates the language invariant", ?_⟩
  simp only [typedLoad, layout_eq _ hgood, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localPtr, listIndex, h.allocs]
  simp [Nat.ne_of_gt hpos, hi, hLi, Allocation.size, hbounds, listSet, subsliceWithLength,
    hset, htk0, decode_int_uninitBytes it hgood, ub]

theorem typedLoad_local_tuple_field1 {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes) (bits b : Nat) (hb : b < 2)
    (hL : L[i]? = some (localAlloc ctx i it (tupleBytes it bits b)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0 + it.size.bytes) = true) :
    ∃ m', typedLoad m (localField1Ptr ctx i it) .Bool align .None =
        .ok (.Bool (decide (b = 1)), m') ∧
      Shape m' ctx frames (ctx.base ++ L) := by
  have hpos := hgood.pos
  have hposI : (1 : Int) ≤ (it.size.bytes : Int) := by omega
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hlen := tupleBytes_length it bits b hpos
  have hset := set_self_of_getElem? L i _ hL
  have ht1 := drop_take_tupleBytes_field1 it bits b
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hsub : ctx.addrs[i]?.getD 0 + (it.size.bytes : Int) - ctx.addrs[i]?.getD 0 =
      (it.size.bytes : Int) := by omega
  have hnonneg : ¬ ((it.size.bytes : Int) < 0) := by omega
  refine ⟨withMem m (ctx.base ++ L)
      ⟨.Load, .None, ctx.addrs.getD i 0 + it.size.bytes, u8Ty.size⟩, ?_, withMem_shape h _⟩
  simp only [typedLoad, layout_bool, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localField1Ptr, listIndex, h.allocs]
  simp [hu8, Nat.ne_of_gt hpos, hposI, hi, hLi, Allocation.size, hlen, hsub, hnonneg,
    Int.toNat_natCast, listSet, subsliceWithLength, hset, ht1,
    decode_bool b hb, checkValue_bool, withMem]

theorem typedLoad_local_tuple_field1_uninit {m : Mach} {ctx : Ctx} {frames : List Frame}
    {L : List Gen.Allocation} (h : Shape m ctx frames (ctx.base ++ L)) (i : Nat) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes)
    (hL : L[i]? = some (localAlloc ctx i it (List.replicate (it.size.bytes + it.size.bytes) .Uninit)))
    (align : Align) (hal : Align.is_aligned align (ctx.addrs.getD i 0 + it.size.bytes) = true) :
    ∃ msg, typedLoad m (localField1Ptr ctx i it) .Bool align .None = .error (.ub msg) := by
  have hpos := hgood.pos
  have hposI : (1 : Int) ≤ (it.size.bytes : Int) := by omega
  obtain ⟨hi, hLi⟩ := List.getElem?_eq_some_iff.mp hL
  have hset := set_self_of_getElem? L i _ hL
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hmin1 : min 1 it.size.bytes = 1 := Nat.min_eq_left (by omega)
  have hdec1 : Type.decode .Bool [Gen.AbstractByte.Uninit] = .ok none := rfl
  have hsub : ctx.addrs[i]?.getD 0 + (it.size.bytes : Int) - ctx.addrs[i]?.getD 0 =
      (it.size.bytes : Int) := by omega
  have hnonneg : ¬ ((it.size.bytes : Int) < 0) := by omega
  refine ⟨"load at type but the data in memory violates the language invariant", ?_⟩
  simp only [typedLoad, layout_bool, LayoutStrategy.expect_size, CM.load, BM.load, hal,
    BM.check_ptr, localField1Ptr, listIndex, h.allocs]
  simp [hu8, Nat.ne_of_gt hpos, hposI, hi, hLi, Allocation.size, hsub, hnonneg,
    Int.toNat_natCast, listSet, subsliceWithLength, hset, hmin1, hdec1, ub]

/-! ## Operands and rvalues -/

/-- The bit pattern an Anneal fragment operand evaluates to, or `none` when
reading it is UB (an uninitialized local). -/
def opBits (locals : List LocalSlot) : Operand → Option Nat
  | .copy ⟨j, []⟩ =>
    match locals[j]? with
    | some (.init (.scalar sc)) => some sc.bits
    | _ => none
  | .copy ⟨j, [.field 0 _]⟩ =>
    match locals[j]? with
    | some (.init (.aggregate 0 [.scalar sc0, .scalar _])) => some sc0.bits
    | _ => none
  | .copy ⟨j, [.field 1 _]⟩ =>
    match locals[j]? with
    | some (.init (.aggregate 0 [.scalar _, .scalar sc1])) => some sc1.bits
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
  simp [evalUnOp, evalIntUnOp, checkValue_int hrep]

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
  | .copy ⟨_, []⟩, h | .copy ⟨_, [.field 0 _]⟩, h =>
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
  addrs : ∀ (i : Nat) d, body.localDecls[i]? = some d →
    AddrOk (ctx.addrs.getD i 0) (itOf d)

theorem FrameOk.decl_scalar {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) :
    scalarTypeOf d.ty = some (tyOf d) :=
  ((translateFn_spec body f h.hf).2.1 i d hd).1

theorem FrameOk.decl_localTy {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) : LocalTy (tyOf d) (itOf d) :=
  localTy_of_decl (h.decl_scalar i d hd)

theorem FrameOk.decl_good {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {locals : List LocalSlot}
    {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt) (i : Nat) (d : LocalDecl)
    (hd : body.localDecls[i]? = some d) : GoodSize (itOf d).size.bytes :=
  (h.decl_localTy i d hd).good

theorem FrameOk.localAllocs_get {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (_h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (slot : LocalSlot) (hd : body.localDecls[i]? = some d)
    (hs : locals[i]? = some slot) :
    (localAllocs ctx body.localDecls locals)[i]? =
      some (localAlloc ctx i (itOf d) (declSlotData d slot)) := by
  simpa [localAllocs] using localAllocsFrom_getElem? ctx 0 body.localDecls locals i d slot hd hs

theorem FrameOk.slot_exists {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (hi : i < body.localDecls.length) :
    ∃ d slot, body.localDecls[i]? = some d ∧ locals[i]? = some slot := by
  refine ⟨body.localDecls[i], locals[i]'(by rw [h.nlocals]; exact hi), by simp [hi], by simp⟩

theorem fragTy_of_scalarTypeOf {d : LocalDecl} {T : Gen.Type} {it : Gen.IntType}
    (hs : scalarTypeOf d.ty = some T) (hT : FragTy T it) :
    FragTy (tyOf d) (itOf d) := by
  rcases scalarTypeOf_cases hs with ⟨hb, _⟩ | ⟨it', hit, _⟩ | ⟨ho, _⟩ | ⟨_, _, rfl⟩
  · obtain ⟨h1, h2⟩ := tyOf_bool hb; rw [h1, h2]; exact .bool
  · obtain ⟨h1, h2⟩ := tyOf_int hit; rw [h1, h2]; exact .int it' (intTypeOf_good hit)
  · obtain ⟨h1, h2⟩ := tyOf_ordering ho; rw [h1, h2]; exact .ordering
  · cases hT

/-- A fragment operand of MiniRust type `T`: the common shape of `operandOk`
(integers) and `operandOkB` (`bool`), including single-level field projections
`.field 0` and `.field 1` on `(Int, bool)` tuple locals. -/
def OperandOkT (decls : List LocalDecl) (T : Gen.Type) : Operand → Prop
  | .copy ⟨j, []⟩ => j < decls.length ∧ operandType decls (.copy ⟨j, []⟩) = some T
  | .copy ⟨j, [.field 0 fTy]⟩ =>
    j < decls.length ∧ operandType decls (.copy ⟨j, [.field 0 fTy]⟩) = some T
  | .copy ⟨j, [.field 1 fTy]⟩ =>
    j < decls.length ∧ operandType decls (.copy ⟨j, [.field 1 fTy]⟩) = some T
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
  | .copy ⟨j, [.field 0 fTy]⟩, h =>
    simp only [operandIntType, Option.bind_eq_bind] at h
    simp only [operandType, Option.bind_eq_bind]
    cases hd : decls[j]? with
    | none => simp [hd] at h
    | some d =>
      cases ht : intBoolTupleOf d.ty with
      | none => simp [hd, ht] at h
      | some it' =>
        cases hf : intTypeOf fTy with
        | none => simp [hd, hf] at h
        | some fIt =>
          simp only [hd, ht, hf, Option.bind_some] at h ⊢
          by_cases heq : fIt = it' <;> simp [heq] at h ⊢
          exact h
  | .constant c, h => simp only [operandIntType] at h; exact scalarTypeOf_int h

theorem operandOk_T {decls : List LocalDecl} {it : Gen.IntType} {op : Operand}
    (h : operandOk decls it op = true) : OperandOkT decls (.Int it) op := by
  match op, h with
  | .copy ⟨j, []⟩, h | .copy ⟨j, [.field 0 _]⟩, h =>
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
  | .copy ⟨j, []⟩, h | .copy ⟨j, [.field 1 _]⟩, h =>
    simp only [operandOkB, Bool.and_eq_true, decide_eq_true_eq, operandIsBool_iff] at h
    exact h
  | .constant c, h =>
    simp only [operandOkB, Bool.and_eq_true, operandIsBool_iff] at h
    exact h

theorem operandType_of_operandOkB {decls : List LocalDecl} {op : Operand}
    (h : operandOkB decls op = true) : operandType decls op = some .Bool := by
  have hT := operandOkB_T h
  match op, hT with
  | .copy ⟨_, []⟩, ⟨_, hty⟩ | .copy ⟨_, [.field 1 _]⟩, ⟨_, hty⟩ | .constant _, ⟨hty, _⟩ =>
    exact hty

theorem operandType_of_operandIsOrdering {decls : List LocalDecl} {op : Operand}
    (h : operandIsOrdering decls op = true) : operandType decls op = some orderingTy := by
  match op, h with
  | .copy ⟨j, []⟩, h =>
    simp only [operandIsOrdering] at h
    simp only [operandType]
    cases hd : decls[j]? with
    | none => simp [hd] at h
    | some d => simp [hd] at h ⊢; exact scalarTypeOf_ordering h
  | .constant c, h => simp only [operandIsOrdering] at h; exact scalarTypeOf_ordering h

theorem operandOkO_T {decls : List LocalDecl} {op : Operand}
    (h : operandOkO decls op = true) : OperandOkT decls orderingTy op := by
  match op, h with
  | .copy ⟨j, []⟩, h =>
    simp only [operandOkO, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, operandType_of_operandIsOrdering h.2⟩
  | .constant c, h =>
    simp only [operandOkO, Bool.and_eq_true] at h
    exact ⟨operandType_of_operandIsOrdering h.1, h.2⟩

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
    simp only [translateOperand, translatePlace, Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨d, slot, hd, hs⟩ := h.slot_exists j hj
    have hspec := (translateFn_spec body f h.hf).2.1 j d hd
    simp only [operandType, hd] at hty
    have hTd : tyOf d = T := tyOf_of_scalarTypeOf hty
    have hfragd : FragTy (tyOf d) (itOf d) := fragTy_of_scalarTypeOf hty hT
    have hitd : itOf d = it := hfragd.unique (hTd ▸ hT)
    have hloc := hspec.2
    rw [hTd] at hloc
    have hplace := evalPlace_local h.shape j hj _ hloc
    have hL := h.localAllocs_get j d slot hd hs
    rw [hfragd.declSlotData, hitd] at hL
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
        { h with shape := hshape }⟩
    | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨_, htyT, _⟩, _ =>
      cases hT <;> simp at htyT
  | .copy ⟨j, [.field 0 fTy]⟩, hok, he =>
    obtain ⟨hj, hty⟩ := hok
    have hcast0 : ((0 : Nat) : Int) = 0 := rfl
    simp only [translateOperand, translatePlace, hcast0, Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨d, slot, hd, hs⟩ := h.slot_exists j hj
    simp only [operandType, Option.bind_eq_bind, hd, Option.bind_some] at hty
    cases ht : intBoolTupleOf d.ty with
    | none => simp [ht] at hty
    | some it' =>
      cases hf : intTypeOf fTy with
      | none => simp [hf] at hty
      | some fIt =>
        simp only [ht, hf, Option.bind_some] at hty
        by_cases heq : fIt = it'
        · subst heq
          simp at hty
          subst hty
          cases hT with
          | int _ hgood =>
            obtain ⟨hTd, hitd⟩ := tyOf_tuple ht
            have hspec := (translateFn_spec body f h.hf).2.1 j d hd
            have hloc := hspec.2
            rw [hTd] at hloc
            have haddr : AddrOk (ctx.addrs.getD j 0) it := hitd ▸ h.addrs j d hd
            have hplace := evalPlace_field0 h.shape j hj it hgood hloc haddr
            have hL := h.localAllocs_get j d slot hd hs
            rw [declSlotData_of_some ht, hitd] at hL
            have hslot := h.slots j d slot hd hs
            rw [hTd] at hslot
            match slot, hslot, hL with
            | .uninit, _, hL =>
              refine ⟨fun bits hb => by simp [opBits, hs] at hb, fun _ => ?_⟩
              obtain ⟨msg, hmsg⟩ :=
                typedLoad_local_tuple_field0_uninit h.shape j it hgood hL ⟨1⟩ (isAligned_one _)
              exact ⟨msg, by simp [evalValue, hplace, placeLoad, hmsg]⟩
            | .init (.scalar sc), ⟨_, hb⟩, _ =>
              simp [intBoolTupleTy, ValidBits] at hb
            | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨it'', htyT, _, hb0, _, _⟩, hL =>
              simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
              subst htyT
              refine ⟨fun bits hbits => ?_, fun hnone => by simp [opBits, hs] at hnone⟩
              simp [opBits, hs] at hbits
              subst hbits
              obtain ⟨m', hm', hshape⟩ :=
                typedLoad_local_tuple_field0 h.shape j it hgood sc0.bits sc1.bits hb0 hL ⟨1⟩ (isAligned_one _)
              exact ⟨hb0, m', by simp [evalValue, hplace, placeLoad, hm', valOf],
                { h with shape := hshape }⟩
        · simp [heq] at hty
  | .copy ⟨j, [.field 1 fTy]⟩, hok, he =>
    obtain ⟨hj, hty⟩ := hok
    have hcast1 : ((1 : Nat) : Int) = 1 := rfl
    simp only [translateOperand, translatePlace, hcast1, Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨d, slot, hd, hs⟩ := h.slot_exists j hj
    simp only [operandType, Option.bind_eq_bind, hd, Option.bind_some] at hty
    cases ht : intBoolTupleOf d.ty with
    | none => simp [ht] at hty
    | some it' =>
      simp only [ht, Option.bind_some] at hty
      by_cases hb : isBoolTy fTy = true
      · simp only [hb, ↓reduceIte, Option.some.injEq] at hty
        subst hty
        cases hT with
        | bool =>
          have hgood := intBoolTupleOf_good ht
          obtain ⟨hTd, hitd⟩ := tyOf_tuple ht
          have hspec := (translateFn_spec body f h.hf).2.1 j d hd
          have hloc := hspec.2
          rw [hTd] at hloc
          have hL := h.localAllocs_get j d slot hd hs
          rw [declSlotData_of_some ht, hitd] at hL
          have hlen := tupleSlotData_length it' slot hgood.pos
          have haddr : AddrOk (ctx.addrs.getD j 0) it' := hitd ▸ h.addrs j d hd
          have hplace := evalPlace_field1 h.shape j hj it' hgood hloc _ hL hlen haddr
          have hslot := h.slots j d slot hd hs
          rw [hTd] at hslot
          match slot, hslot, hL with
          | .uninit, _, hL =>
            refine ⟨fun bits hb => by simp [opBits, hs] at hb, fun _ => ?_⟩
            obtain ⟨msg, hmsg⟩ :=
              typedLoad_local_tuple_field1_uninit h.shape j it' hgood hL ⟨1⟩ (isAligned_one _)
            exact ⟨msg, by simp [evalValue, hplace, placeLoad, hmsg]⟩
          | .init (.scalar sc), ⟨_, hb⟩, _ =>
            simp [intBoolTupleTy, ValidBits] at hb
          | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨it'', htyT, _, _, _, hb1⟩, hL =>
            simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
            subst htyT
            refine ⟨fun bits hbits => ?_, fun hnone => by simp [opBits, hs] at hnone⟩
            simp [opBits, hs] at hbits
            subst hbits
            obtain ⟨m', hm', hshape⟩ :=
              typedLoad_local_tuple_field1 h.shape j it' hgood sc0.bits sc1.bits hb1 hL ⟨1⟩ (isAligned_one _)
            exact ⟨hb1, m', by simp [evalValue, hplace, placeLoad, hm', valOf],
              { h with shape := hshape }⟩
      · simp [hb] at hty
  | .constant c, hok, he =>
    obtain ⟨hty, _⟩ := hok
    simp only [operandType] at hty
    rcases scalarTypeOf_cases hty with ⟨hb, hTb⟩ | ⟨it', hit', hTi⟩ | ⟨ho, _⟩ | ⟨_, ht, _⟩
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
    · simp [translateOperand_ordering_const ho] at he
    · simp [translateOperand_tuple_const ht] at he

theorem operandOk_good {decls : List LocalDecl} {it : Gen.IntType} {op : Operand}
    (hok : operandOk decls it op = true) : GoodSize it.size.bytes := by
  have hit := operandIntType_of_operandOk hok
  match op, hit with
  | .copy ⟨j, []⟩, hit =>
    simp only [operandIntType] at hit
    cases hd : decls[j]? with
    | none => simp [hd] at hit
    | some d => simp [hd] at hit; exact intTypeOf_good hit
  | .copy ⟨j, [.field 0 fTy]⟩, hit =>
    simp only [operandIntType, Option.bind_eq_bind] at hit
    cases hd : decls[j]? with
    | none => simp [hd] at hit
    | some d =>
      cases ht : intBoolTupleOf d.ty with
      | none => simp [hd, ht] at hit
      | some it' =>
        cases hf : intTypeOf fTy with
        | none => simp [hd, hf] at hit
        | some fIt =>
          simp only [hd, ht, hf, Option.bind_some] at hit
          by_cases heq : fIt = it'
          · simp [heq] at hit; subst hit; exact intBoolTupleOf_good ht
          · simp [heq] at hit
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
  have hty := operandType_of_operandOkB hok
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
        simp [evalValue, hm1, evalUnOp, heval, hbring, checkValue_int hrep]
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
  have hT := (h.decl_localTy i d hd).of_validBits hr
  have hspec := (translateFn_spec body f h.hf).2.1 i d hd
  have hplace := evalPlace_local h.shape i hi _ hspec.2
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  have hL1 := h1.localAllocs_get i d slot hd hs
  rw [hT.declSlotData] at hL1
  have hst := typedStore_local_frag h1.shape i hT _ r hr hL1 (slotData_length _ _) ⟨1⟩
    (isAligned_one _)
  have hset := localAllocsFrom_set ctx 0 body.localDecls locals i d
    (.init (.scalar ⟨r, (itOf d).size.bytes⟩)) hd
  simp only [Nat.zero_add, hT.declSlotData, slotData] at hset
  refine ⟨withMem m1 (ctx.base ++ localAllocs ctx body.localDecls
      (locals.set i (.init (.scalar ⟨r, (itOf d).size.bytes⟩))))
      ⟨.Store, .None, ctx.addrs.getD i 0, (itOf d).size⟩, ?_, ?_⟩
  · have hst' := hst
    simp only [localAllocs] at hst'
    rw [hset] at hst'
    simp [evalStatement, hplace, hm1, placeStore, hst', localAllocs]
  refine ⟨h.hf, withMem_shape h1.shape _, by simp [h.nlocals], ?_, h.addrs⟩
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

/-- `Machine::eval_statement` on a translated fragment `PlaceMention` (including
field projections `_i.0` and `_i.1` on an `(Int, bool)` 2-tuple local). -/
theorem evalStatement_placeMention_place {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (p : Place) (hp : placeOk body.localDecls p = true) (pe : Gen.PlaceExpr)
    (hpe : translatePlace p = some pe) :
    evalStatement m (.PlaceMention pe) = .ok m ∧ p.local_ < body.localDecls.length := by
  match p, hp, hpe with
  | ⟨i, []⟩, hp, hpe =>
    simp only [placeOk, decide_eq_true_eq] at hp
    simp only [translatePlace, Option.some.injEq] at hpe
    subst hpe
    exact ⟨evalStatement_placeMention h i hp, hp⟩
  | ⟨i, [.field 0 fieldTy]⟩, hp, hpe =>
    simp only [placeOk, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨hi, ht⟩ := hp
    simp only [translatePlace, Option.some.injEq] at hpe
    subst hpe
    obtain ⟨d, slot, hd, _⟩ := h.slot_exists i hi
    simp only [hd] at ht
    cases htup : intBoolTupleOf d.ty with
    | none => simp [htup] at ht
    | some it =>
      cases hf : intTypeOf fieldTy with
      | none => simp [htup, hf] at ht
      | some fit =>
        simp only [htup, hf, decide_eq_true_eq] at ht
        subst ht
        obtain ⟨hTd, hitd⟩ := tyOf_tuple htup
        have hspec := (translateFn_spec body f h.hf).2.1 i d hd
        have hloc := hspec.2
        rw [hTd] at hloc
        have haddr := h.addrs i d hd
        rw [hitd] at haddr
        have hplace := evalPlace_field0 h.shape i hi fit (intBoolTupleOf_good htup) hloc haddr
        exact ⟨by simp [evalStatement, hplace], hi⟩
  | ⟨i, [.field 1 fieldTy]⟩, hp, hpe =>
    simp only [placeOk, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨hi, ht⟩ := hp
    simp only [translatePlace, Option.some.injEq] at hpe
    subst hpe
    obtain ⟨d, slot, hd, hs⟩ := h.slot_exists i hi
    simp only [hd, Bool.and_eq_true] at ht
    obtain ⟨htSome, _⟩ := ht
    obtain ⟨it, htup⟩ := Option.isSome_iff_exists.mp htSome
    obtain ⟨hTd, hitd⟩ := tyOf_tuple htup
    have hgood := intBoolTupleOf_good htup
    have hspec := (translateFn_spec body f h.hf).2.1 i d hd
    have hloc := hspec.2
    rw [hTd] at hloc
    have hL := h.localAllocs_get i d slot hd hs
    rw [declSlotData_of_some htup, hitd] at hL
    have haddr := h.addrs i d hd
    rw [hitd] at haddr
    have hlen := tupleSlotData_length it slot hgood.pos
    have hplace := evalPlace_field1 h.shape i hi it hgood hloc _ hL hlen haddr
    exact ⟨by simp [evalStatement, hplace], hi⟩

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
theorem evalBinOp_rel_frag {T : Gen.Type} {it : Gen.IntType} (hT : RelTy T it) (rel : Gen.RelOp)
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
  have hty := operandType_of_operandOkB hok
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

/-- Bitwise evaluation of `BitAnd`, `BitOr`, and `BitXor` on `bool` bits (`0`
or `1`). -/
def boolBitEval : Gen.IntBinOp → Nat → Nat → Nat
  | .BitAnd, x, y => if x = 1 ∧ y = 1 then 1 else 0
  | .BitOr, x, y => if x = 1 ∨ y = 1 then 1 else 0
  | .BitXor, x, y => if (x = 1) ≠ (y = 1) then 1 else 0
  | _, _, _ => 0

theorem boolBitEval_lt (iop : Gen.IntBinOp) (x y : Nat) : boolBitEval iop x y < 2 := by
  unfold boolBitEval
  split <;> try split
  all_goals omega

/-- `build::bool_and`, `build::bool_or`, and `build::bool_xor` on two `bool`
operands: all three transmutes succeed because `0` and `1` are valid `bool`
bytes and their bitwise combinations are also `0` or `1`. -/
theorem evalValue_boolBitOp {op : MirAst.BinOp} {iop : Gen.IntBinOp}
    (hop : translateBoolBitOp op = some iop) (m m1 m2 : Mach) (ea eb : Gen.ValueExpr)
    (x y : Nat) (hx : x < 2) (hy : y < 2)
    (ha : evalValue m ea = .ok ((valOf .Bool x, .Bool), m1))
    (hb : evalValue m1 eb = .ok ((valOf .Bool y, .Bool), m2)) :
    evalValue m (boolBitOp iop ea eb) =
      .ok ((valOf .Bool (boolBitEval iop x y), .Bool), m2) := by
  have ha8 := evalValue_boolToU8 m m1 ea (decide (x = 1)) ha
  have hb8 := evalValue_boolToU8 m1 m2 eb (decide (y = 1)) hb
  cases op <;> simp [translateBoolBitOp] at hop <;> subst hop <;>
    rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;>
    simp [boolBitOp, evalValue, ha8, hb8] <;> rfl

theorem translateRvalue_boolBit {decls : List LocalDecl} {op : MirAst.BinOp} {a b : Operand}
    {e : Gen.ValueExpr} {iop : Gen.IntBinOp} (hop : translateBoolBitOp op = some iop)
    (hty : operandType decls a = some .Bool)
    (he : translateRvalue decls (.binaryOp op a b) = some e) :
    ∃ ea eb, translateOperand a = some ea ∧ translateOperand b = some eb ∧
      e = boolBitOp iop ea eb := by
  have hrel : translateRelOp op = none := by
    cases op <;> simp [translateBoolBitOp] at hop <;> rfl
  have hbin : translateBinOp op = some iop := by
    cases op <;> simp [translateBoolBitOp] at hop <;> subst hop <;> rfl
  simp only [translateRvalue, Option.bind_eq_bind] at he
  cases hea : translateOperand a with
  | none => simp [hea] at he
  | some ea =>
    cases heb : translateOperand b with
    | none => simp [hea, heb] at he
    | some eb =>
      simp [hea, heb, hrel, hbin, hty, hop] at he
      exact ⟨ea, eb, rfl, rfl, he.symm⟩

/-- The bit pattern an Anneal fragment rvalue of type `bool` evaluates to, or
`none` when evaluating it is UB. -/
def rvBitsB (decls : List LocalDecl) (locals : List LocalSlot) : Rvalue → Option Nat
  | .use op => opBits locals op
  | .unaryOp .not op => (opBits locals op).map (fun x => 1 - x)
  | .binaryOp op a b =>
    match translateRelOp op with
    | some rel => do
      let T ← operandType decls a
      let x ← opBits locals a
      let y ← opBits locals b
      pure (if relBool rel (cmpOf T x y) then 1 else 0)
    | none => do
      let iop ← translateBoolBitOp op
      let x ← opBits locals a
      let y ← opBits locals b
      pure (boolBitEval iop x y)
  | _ => none

/-- The operands of a fragment comparison have one fragment type. -/
theorem relOperandsOk_spec {decls : List LocalDecl} {a b : Operand}
    (h : relOperandsOk decls a b = true) :
    ∃ T it, RelTy T it ∧ operandType decls a = some T ∧ OperandOkT decls T a ∧
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
    cases hrel : translateRelOp op with
    | some rel =>
      simp [rvalueOkB, hrel] at hok
      obtain ⟨ea, eb, hea, heb, rfl⟩ := translateRvalue_rel hrel he
      obtain ⟨T, it, hT, htyA, hokA, hokB⟩ := relOperandsOk_spec hok
      obtain ⟨hasome, hanone⟩ := evalValue_operandT h hT.frag a hokA ea hea
      cases hxa : opBits locals a with
      | none =>
        refine ⟨fun r hr => by simp [rvBitsB, hrel, htyA, hxa] at hr, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hanone hxa
        exact ⟨msg, by simp [evalValue, hmsg]⟩
      | some x =>
        obtain ⟨_, m1, hm1, h1⟩ := hasome x hxa
        obtain ⟨hbsome, hbnone⟩ := evalValue_operandT h1 hT.frag b hokB eb heb
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
    | none =>
      simp [rvalueOkB, hrel] at hok
      obtain ⟨⟨hbitSome, hokA'⟩, hokB'⟩ := hok
      cases hiop : translateBoolBitOp op with
      | none => simp [hiop] at hbitSome
      | some iop =>
        have hokA := operandOkB_T hokA'
        have hokB := operandOkB_T hokB'
        have htyA := operandType_of_operandOkB hokA'
        obtain ⟨ea, eb, hea, heb, rfl⟩ := translateRvalue_boolBit hiop htyA he
        obtain ⟨hasome, hanone⟩ := evalValue_operandT h .bool a hokA ea hea
        cases hxa : opBits locals a with
        | none =>
          refine ⟨fun r hr => by simp [rvBitsB, hrel, hiop, hxa] at hr, fun _ => ?_⟩
          obtain ⟨msg, hmsg⟩ := hanone hxa
          exact ⟨msg, by simp [boolBitOp, boolToU8, evalValue, hmsg]⟩
        | some x =>
          obtain ⟨hx, m1, hm1, h1⟩ := hasome x hxa
          have hx2 : x < 2 := by simpa [ValidBits] using hx
          have ha8 := evalValue_boolToU8 m m1 ea (decide (x = 1)) hm1
          obtain ⟨hbsome, hbnone⟩ := evalValue_operandT h1 .bool b hokB eb heb
          cases hyb : opBits locals b with
          | none =>
            refine ⟨fun r hr => by simp [rvBitsB, hrel, hiop, hxa, hyb] at hr, fun _ => ?_⟩
            obtain ⟨msg, hmsg⟩ := hbnone hyb
            refine ⟨msg, by simp [boolBitOp, evalValue, ha8]; simp [boolToU8, evalValue, hmsg]⟩
          | some y =>
            obtain ⟨hy, m2, hm2, h2⟩ := hbsome y hyb
            have hy2 : y < 2 := by simpa [ValidBits] using hy
            refine ⟨fun r hr => ?_, fun hr => by simp [rvBitsB, hrel, hiop, hxa, hyb] at hr⟩
            simp [rvBitsB, hrel, hiop, hxa, hyb] at hr
            subst hr
            exact ⟨boolBitEval_lt iop x y, m2,
              evalValue_boolBitOp hiop m m1 m2 ea eb x y hx2 hy2 hm1 hm2, h2⟩
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

/-! ## `Ordering` rvalues -/

/-- The tag of the `Ordering` variant for a comparison outcome: `Less` is the
`i8` `-1` (bit pattern `255`), `Equal` is `0`, and `Greater` is `1`. -/
def ordBits : Ordering → Nat
  | .lt => 255
  | .eq => 0
  | .gt => 1

theorem validBits_ordBits (o : Ordering) : ValidBits orderingTy (ordBits o) := by
  cases o <;> exact (validBits_iff _ _).mp rfl

/-- The transmute of `translateCmp` turns the `i8` that `RelOp::Cmp` returns
for the outcome `o` into the `Ordering` variant with tag `ordBits o`. -/
theorem evalUnOp_transmute_ordering (o : Ordering) :
    evalUnOp (.Cast (.Transmute orderingTy)) (evalRelOp .Cmp o) =
      .ok (valOf orderingTy (ordBits o), orderingTy) := by
  cases o <;> rfl

/-- `BinOp::Rel(RelOp::Cmp)` on two values of one comparable fragment type. -/
theorem evalBinOp_cmp_frag {T : Gen.Type} {it : Gen.IntType} (hT : RelTy T it) (x y : Nat) :
    evalBinOp (.Rel .Cmp) (valOf T x, T) (valOf T y, T) = .ok (evalRelOp .Cmp (cmpOf T x y)) := by
  cases hT <;> simp [evalBinOp, valOf, cmpOf]

/-- `translateCmp` on two operands of one comparable fragment type evaluates
to the `Ordering` variant of their comparison. -/
theorem evalValue_translateCmp {T : Gen.Type} {it : Gen.IntType} (hT : RelTy T it)
    (m m1 m2 : Mach) (ea eb : Gen.ValueExpr) (x y : Nat)
    (ha : evalValue m ea = .ok ((valOf T x, T), m1))
    (hb : evalValue m1 eb = .ok ((valOf T y, T), m2)) :
    evalValue m (translateCmp ea eb) =
      .ok ((valOf orderingTy (ordBits (cmpOf T x y)), orderingTy), m2) := by
  simp only [translateCmp, evalValue, ha, hb, ok_bind, evalBinOp_cmp_frag hT x y]
  generalize cmpOf T x y = o
  cases o <;> rfl

theorem translateRvalue_cmp {decls : List LocalDecl} {a b : Operand} {e : Gen.ValueExpr}
    (he : translateRvalue decls (.binaryOp .cmp a b) = some e) :
    ∃ ea eb, translateOperand a = some ea ∧ translateOperand b = some eb ∧
      e = translateCmp ea eb := by
  simp only [translateRvalue, Option.bind_eq_bind] at he
  cases hea : translateOperand a with
  | none => simp [hea] at he
  | some ea =>
    cases heb : translateOperand b with
    | none => simp [hea, heb] at he
    | some eb =>
      simp [hea, heb, translateRelOp, translateBinOp, translateCheckedBinOp] at he
      exact ⟨ea, eb, rfl, rfl, he.symm⟩

/-- A fragment rvalue of type `Ordering` is either a `Use` of an `Ordering`
operand or a three-way comparison `Cmp`. -/
theorem rvalueOkO_spec {decls : List LocalDecl} {rv : Rvalue} (h : rvalueOkO decls rv = true) :
    (∃ op, rv = .use op ∧ operandOkO decls op = true) ∨
    (∃ a b, rv = .binaryOp .cmp a b ∧ relOperandsOk decls a b = true) := by
  unfold rvalueOkO at h
  split at h
  · exact .inl ⟨_, rfl, h⟩
  · exact .inr ⟨_, _, rfl, h⟩
  · simp at h

/-- The bit pattern an Anneal fragment rvalue of type `Ordering` evaluates to,
or `none` when evaluating it is UB. -/
def rvBitsO (decls : List LocalDecl) (locals : List LocalSlot) : Rvalue → Option Nat
  | .use op => opBits locals op
  | .binaryOp .cmp a b => do
    let T ← operandType decls a
    let x ← opBits locals a
    let y ← opBits locals b
    pure (ordBits (cmpOf T x y))
  | _ => none

/-- Evaluating a translated fragment rvalue of type `Ordering`. -/
theorem evalValue_rvalueO {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (rv : Rvalue) (hok : rvalueOkO body.localDecls rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.localDecls rv = some e) :
    (∀ r, rvBitsO body.localDecls locals rv = some r →
      ValidBits orderingTy r ∧
      ∃ m', evalValue m e = .ok ((valOf orderingTy r, orderingTy), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (rvBitsO body.localDecls locals rv = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  rcases rvalueOkO_spec hok with ⟨op, rfl, hokOp⟩ | ⟨a, b, rfl, hops⟩
  · simp only [translateRvalue] at he
    exact evalValue_operandT h .ordering op (operandOkO_T hokOp) e he
  · obtain ⟨ea, eb, hea, heb, rfl⟩ := translateRvalue_cmp he
    obtain ⟨T, it, hT, htyA, hokA, hokB⟩ := relOperandsOk_spec hops
    obtain ⟨hasome, hanone⟩ := evalValue_operandT h hT.frag a hokA ea hea
    cases hxa : opBits locals a with
    | none =>
      refine ⟨fun r hr => by simp [rvBitsO, htyA, hxa] at hr, fun _ => ?_⟩
      obtain ⟨msg, hmsg⟩ := hanone hxa
      exact ⟨msg, by simp [translateCmp, evalValue, hmsg]⟩
    | some x =>
      obtain ⟨_, m1, hm1, h1⟩ := hasome x hxa
      obtain ⟨hbsome, hbnone⟩ := evalValue_operandT h1 hT.frag b hokB eb heb
      cases hyb : opBits locals b with
      | none =>
        refine ⟨fun r hr => by simp [rvBitsO, htyA, hxa, hyb] at hr, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hbnone hyb
        exact ⟨msg, by simp [translateCmp, evalValue, hm1, hmsg]⟩
      | some y =>
        obtain ⟨_, m2, hm2, h2⟩ := hbsome y hyb
        refine ⟨fun r hr => ?_, fun hr => by simp [rvBitsO, htyA, hxa, hyb] at hr⟩
        simp [rvBitsO, htyA, hxa, hyb] at hr
        subst hr
        exact ⟨validBits_ordBits _, m2, evalValue_translateCmp hT m m1 m2 ea eb x y hm1 hm2, h2⟩

/-- `Machine::eval_statement` on a translated fragment assignment to an
`Ordering` local. -/
theorem evalStatement_assignO {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (hord : isOrderingTy d.ty = true)
    (rv : Rvalue) (hok : rvalueOkO body.localDecls rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.localDecls rv = some e) :
    (∀ r, rvBitsO body.localDecls locals rv = some r →
      ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
        FrameOk body f ctx (locals.set i (.init (.scalar ⟨r, (itOf d).size.bytes⟩))) m' blk stmt) ∧
    (rvBitsO body.localDecls locals rv = none →
      ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have htyd : tyOf d = orderingTy := (tyOf_ordering hord).1
  have hspec := (translateFn_spec body f h.hf).2.1 i d hd
  have hplace := evalPlace_local h.shape i hi _ hspec.2
  obtain ⟨hrok, hrnone⟩ := evalValue_rvalueO h rv hok e he
  refine ⟨fun r hr => ?_, fun hnone => ?_⟩
  · obtain ⟨hrlt, m1, hm1, h1⟩ := hrok r hr
    exact evalStatement_assign_of h i d hd e r (by rw [htyd]; exact hrlt) _ m1
      (by rw [htyd]; exact hm1) h1
  · obtain ⟨msg, hmsg⟩ := hrnone hnone
    exact ⟨msg, by simp [evalStatement, hplace, hmsg]⟩

/-! ## `(Int, bool)` 2-tuple rvalues and checked integer arithmetic -/

/-- Mathematical integer arithmetic of `eval_int_bin_op_with_overflow`. -/
def intCheckedArith : Gen.IntBinOpWithOverflow → Int → Int → Int
  | .Add, l, r => l + r
  | .Sub, l, r => l - r
  | .Mul, l, r => l * r

/-- `Machine::eval_bin_op` on `BinOp::IntWithOverflow(cop)` returns the
2-tuple `(res_wrapped, !can_represent(res))` at `intBoolTupleTy it`. -/
theorem evalBinOp_intWithOverflow (cop : Gen.IntBinOpWithOverflow) (it : Gen.IntType)
    (hgood : GoodSize it.size.bytes) (l r : Int) :
    evalBinOp (.IntWithOverflow cop) (.Int l, .Int it) (.Int r, .Int it) =
      let res := intCheckedArith cop l r
      let wrappedBits := (res % 2 ^ (8 * it.size.bytes)).toNat
      let ovfBit := if IntType.can_represent it res then 0 else 1
      .ok (tupleVal it wrappedBits ovfBit, intBoolTupleTy it) := by
  let res := intCheckedArith cop l r
  have heval : evalIntBinOpWithOverflow cop l r = res := by cases cop <;> rfl
  have hovf : decide ((if IntType.can_represent it res = true then 0 else 1) = 1) =
      !IntType.can_represent it res := by
    cases IntType.can_represent it res <;> rfl
  simp only [evalBinOp, heval, withOverflow_eq it hgood,
    bringInBounds_eq_intFromBits it hgood res, tupleVal, ← hovf]
  rfl

/-- Pair of bit patterns `(bits, b)` an Anneal 2-tuple operand evaluates to, or
`none` when reading it is UB. -/
def opTupleBits (locals : List LocalSlot) : Operand → Option (Nat × Nat)
  | .copy ⟨j, []⟩ =>
    match locals[j]? with
    | some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) => some (sc0.bits, sc1.bits)
    | _ => none
  | _ => none

/-- Pair of bit patterns `(bits, b)` an Anneal 2-tuple rvalue of type
`(it, bool)` evaluates to, or `none` when evaluating it is UB. -/
def rvTupleBits (locals : List LocalSlot) (it : Gen.IntType) : Rvalue → Option (Nat × Nat)
  | .use op => opTupleBits locals op
  | .binaryOp op a b => do
    let cop ← translateCheckedBinOp op
    let x ← opBits locals a
    let y ← opBits locals b
    let res := intCheckedArith cop (intFromBits x it) (intFromBits y it)
    let wrappedBits := (res % 2 ^ (8 * it.size.bytes)).toNat
    let ovfBit := if IntType.can_represent it res then 0 else 1
    pure (wrappedBits, ovfBit)
  | .aggregate .tuple [a, b] => do
    let x ← opBits locals a
    let y ← opBits locals b
    pure (x, y)
  | _ => none

theorem translateRelOp_of_translateCheckedBinOp {op : MirAst.BinOp}
    {cop : Gen.IntBinOpWithOverflow} (h : translateCheckedBinOp op = some cop) :
    translateRelOp op = none := by
  cases op <;> simp_all [translateCheckedBinOp, translateRelOp]

theorem translateBinOp_of_translateCheckedBinOp {op : MirAst.BinOp}
    {cop : Gen.IntBinOpWithOverflow} (h : translateCheckedBinOp op = some cop) :
    translateBinOp op = none := by
  cases op <;> simp_all [translateCheckedBinOp, translateBinOp]

theorem translateRvalue_checked {decls : List LocalDecl} {op : MirAst.BinOp} {a b : Operand}
    {e : Gen.ValueExpr} {cop : Gen.IntBinOpWithOverflow}
    (hcop : translateCheckedBinOp op = some cop)
    (he : translateRvalue decls (.binaryOp op a b) = some e) :
    ∃ ea eb, translateOperand a = some ea ∧ translateOperand b = some eb ∧
      e = .BinOp (.IntWithOverflow cop) ea eb := by
  simp only [translateRvalue, Option.bind_eq_bind, translateRelOp_of_translateCheckedBinOp hcop,
    translateBinOp_of_translateCheckedBinOp hcop, hcop] at he
  cases hea : translateOperand a with
  | none => simp [hea] at he
  | some ea =>
    cases heb : translateOperand b with
    | none => simp [hea, heb] at he
    | some eb => simp [hea, heb] at he; exact ⟨ea, eb, rfl, rfl, he.symm⟩

theorem translateRvalue_tuple_agg {decls : List LocalDecl} {it : Gen.IntType} {a b : Operand}
    {e : Gen.ValueExpr} (hoka : operandOk decls it a = true)
    (he : translateRvalue decls (.aggregate .tuple [a, b]) = some e) :
    ∃ ea eb, translateOperand a = some ea ∧ translateOperand b = some eb ∧
      e = .Tuple [ea, eb] (intBoolTupleTy it) := by
  have hit := operandIntType_of_operandOk hoka
  simp only [translateRvalue, Option.bind_eq_bind, hit] at he
  cases hea : translateOperand a with
  | none => simp [hea] at he
  | some ea =>
    cases heb : translateOperand b with
    | none => simp [hea, heb] at he
    | some eb => simp [hea, heb] at he; exact ⟨ea, eb, rfl, rfl, he.symm⟩

/-- Evaluating a translated fragment 2-tuple operand of type `intBoolTupleTy it`. -/
theorem evalValue_operandTuple {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes) (op : Operand)
    (hok : operandOkTuple body.localDecls it op = true) (e : Gen.ValueExpr)
    (he : translateOperand op = some e) :
    (∀ bits b, opTupleBits locals op = some (bits, b) →
      bits < 2 ^ (8 * it.size.bytes) ∧ b < 2 ∧
      ∃ m', evalValue m e = .ok ((tupleVal it bits b, intBoolTupleTy it), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (opTupleBits locals op = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  match op, hok, he with
  | .copy ⟨j, []⟩, hok, he =>
    simp only [operandOkTuple, operandTupleIntType, Option.bind_eq_bind, Bool.and_eq_true,
      decide_eq_true_eq] at hok
    obtain ⟨hj, ht⟩ := hok
    simp only [translateOperand, translatePlace, Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨d, slot, hd, hs⟩ := h.slot_exists j hj
    simp only [hd, Option.bind_some, decide_eq_true_eq] at ht
    obtain ⟨hTd, hitd⟩ := tyOf_tuple ht
    have hspec := (translateFn_spec body f h.hf).2.1 j d hd
    have hloc := hspec.2
    rw [hTd] at hloc
    have hplace := evalPlace_local h.shape j hj _ hloc
    have hL := h.localAllocs_get j d slot hd hs
    rw [declSlotData_of_some ht, hitd] at hL
    have hslot := h.slots j d slot hd hs
    rw [hTd] at hslot
    match slot, hslot, hL with
    | .uninit, _, hL =>
      refine ⟨fun bits b hbb => by simp [opTupleBits, hs] at hbb, fun _ => ?_⟩
      obtain ⟨msg, hmsg⟩ :=
        typedLoad_local_tuple_uninit h.shape j it hgood hL ⟨1⟩ (isAligned_one _)
      exact ⟨msg, by simp [evalValue, hplace, placeLoad, hmsg]⟩
    | .init (.scalar sc), ⟨_, hb⟩, _ =>
      simp [intBoolTupleTy, ValidBits] at hb
    | .init (.aggregate 0 [.scalar sc0, .scalar sc1]), ⟨it', htyT, _, hb0, _, hb1⟩, hL =>
      simp only [tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
      subst htyT
      refine ⟨fun bits b hbb => ?_, fun hnone => by simp [opTupleBits, hs] at hnone⟩
      simp [opTupleBits, hs] at hbb
      rcases hbb with ⟨rfl, rfl⟩
      obtain ⟨m', hm', hshape⟩ :=
        typedLoad_local_tuple h.shape j it hgood sc0.bits sc1.bits hb0 hb1 hL ⟨1⟩ (isAligned_one _)
      exact ⟨hb0, hb1, m', by simp [evalValue, hplace, placeLoad, hm'],
        { h with shape := hshape }⟩

/-- Evaluating a translated fragment rvalue of 2-tuple type `intBoolTupleTy it`. -/
theorem evalValue_rvalueTuple {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes) (rv : Rvalue)
    (hok : rvalueOkTuple body.localDecls it rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.localDecls rv = some e) :
    (∀ bits b, rvTupleBits locals it rv = some (bits, b) →
      bits < 2 ^ (8 * it.size.bytes) ∧ b < 2 ∧
      ∃ m', evalValue m e = .ok ((tupleVal it bits b, intBoolTupleTy it), m') ∧
        FrameOk body f ctx locals m' blk stmt) ∧
    (rvTupleBits locals it rv = none → ∃ msg, evalValue m e = .error (.ub msg)) := by
  match rv, hok, he with
  | .use op, hok, he =>
    simp only [rvalueOkTuple] at hok
    simp only [translateRvalue] at he
    exact evalValue_operandTuple h it hgood op hok e he
  | .binaryOp op a b, hok, he =>
    simp only [rvalueOkTuple, Bool.and_eq_true] at hok
    obtain ⟨⟨hcopSome, hoka⟩, hokb⟩ := hok
    cases hcop : translateCheckedBinOp op with
    | none => simp [hcop] at hcopSome
    | some cop =>
      obtain ⟨ea, eb, hea, heb, rfl⟩ := translateRvalue_checked hcop he
      obtain ⟨haok, hanone⟩ := evalValue_operand h it a hoka ea hea
      cases hxa : opBits locals a with
      | none =>
        refine ⟨fun bits b' hbb => by simp [rvTupleBits, hcop, hxa] at hbb, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hanone hxa
        exact ⟨msg, by simp [evalValue, hmsg]⟩
      | some x =>
        obtain ⟨_, m1, hm1, h1⟩ := haok x hxa
        obtain ⟨hbok, hbnone⟩ := evalValue_operand h1 it b hokb eb heb
        cases hyb : opBits locals b with
        | none =>
          refine ⟨fun bits b' hbb => by simp [rvTupleBits, hcop, hxa, hyb] at hbb, fun _ => ?_⟩
          obtain ⟨msg, hmsg⟩ := hbnone hyb
          exact ⟨msg, by simp [evalValue, hm1, hmsg]⟩
        | some y =>
          obtain ⟨_, m2, hm2, h2⟩ := hbok y hyb
          refine ⟨fun bits b' hbb => ?_, fun hnone => by simp [rvTupleBits, hcop, hxa, hyb] at hnone⟩
          simp [rvTupleBits, hcop, hxa, hyb] at hbb
          rcases hbb with ⟨rfl, rfl⟩
          have hpos := two_pow_pos (8 * it.size.bytes)
          let res := intCheckedArith cop (intFromBits x it) (intFromBits y it)
          have h0 := Int.emod_nonneg res (Int.ne_of_gt hpos)
          have hlt := Int.emod_lt_of_pos res hpos
          have hbits : (res % 2 ^ (8 * it.size.bytes)).toNat < 2 ^ (8 * it.size.bytes) := by
            have : (((res % 2 ^ (8 * it.size.bytes)).toNat : Int)) < 2 ^ (8 * it.size.bytes) := by
              rw [Int.toNat_of_nonneg h0]; exact hlt
            exact_mod_cast this
          have hb' : (if IntType.can_represent it res then 0 else 1) < 2 := by split <;> omega
          exact ⟨hbits, hb', m2,
            by simp [evalValue, hm1, hm2, evalBinOp_intWithOverflow cop it hgood], h2⟩
  | .aggregate .tuple [a, b], hok, he =>
    simp only [rvalueOkTuple, Bool.and_eq_true] at hok
    obtain ⟨hoka, hokb⟩ := hok
    obtain ⟨ea, eb, hea, heb, rfl⟩ := translateRvalue_tuple_agg hoka he
    obtain ⟨haok, hanone⟩ := evalValue_operand h it a hoka ea hea
    cases hxa : opBits locals a with
    | none =>
      refine ⟨fun bits b' hbb => by simp [rvTupleBits, hxa] at hbb, fun _ => ?_⟩
      obtain ⟨msg, hmsg⟩ := hanone hxa
      exact ⟨msg, by simp [evalValue, evalValues, hmsg]⟩
    | some x =>
      obtain ⟨hx, m1, hm1, h1⟩ := haok x hxa
      obtain ⟨hbok, hbnone⟩ := evalValue_operandT h1 .bool b (operandOkB_T hokb) eb heb
      cases hyb : opBits locals b with
      | none =>
        refine ⟨fun bits b' hbb => by simp [rvTupleBits, hxa, hyb] at hbb, fun _ => ?_⟩
        obtain ⟨msg, hmsg⟩ := hbnone hyb
        exact ⟨msg, by simp [evalValue, evalValues, hm1, hmsg]⟩
      | some y =>
        obtain ⟨hy, m2, hm2, h2⟩ := hbok y hyb
        have hy2 : y < 2 := by simpa [ValidBits] using hy
        refine ⟨fun bits b' hbb => ?_, fun hnone => by simp [rvTupleBits, hxa, hyb] at hnone⟩
        simp [rvTupleBits, hxa, hyb] at hbb
        rcases hbb with ⟨rfl, rfl⟩
        refine ⟨hx, hy2, m2, ?_, h2⟩
        simp [evalValue, evalValues, hm1, hm2, valOf, tupleVal]

/-- `Machine::eval_statement` on a translated fragment assignment to an
`(it, bool)` 2-tuple local. -/
theorem evalStatement_assignTuple {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (htup : intBoolTupleOf d.ty = some (itOf d)) (rv : Rvalue)
    (hok : rvalueOkTuple body.localDecls (itOf d) rv = true) (e : Gen.ValueExpr)
    (he : translateRvalue body.localDecls rv = some e) :
    (∀ bits b, rvTupleBits locals (itOf d) rv = some (bits, b) →
      ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
        FrameOk body f ctx
          (locals.set i (.init (.aggregate 0 [.scalar ⟨bits, (itOf d).size.bytes⟩, .scalar ⟨b, 1⟩])))
          m' blk stmt) ∧
    (rvTupleBits locals (itOf d) rv = none →
      ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood := h.decl_good i d hd
  have htyd : tyOf d = intBoolTupleTy (itOf d) := (tyOf_tuple htup).1
  have hspec := (translateFn_spec body f h.hf).2.1 i d hd
  have hplace := evalPlace_local h.shape i hi _ hspec.2
  obtain ⟨hrok, hrnone⟩ := evalValue_rvalueTuple h (itOf d) hgood rv hok e he
  refine ⟨fun bits b hbb => ?_, fun hnone => ?_⟩
  · obtain ⟨hbits, hb, m1, hm1, h1⟩ := hrok bits b hbb
    obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
    have hL1 := h1.localAllocs_get i d slot hd hs
    rw [declSlotData_of_some htup] at hL1
    have hlen := tupleSlotData_length (itOf d) slot hgood.pos
    have hst := typedStore_local_tuple h1.shape i (itOf d) hgood _ bits b hbits hb hL1 hlen ⟨1⟩
      (isAligned_one _)
    let newSlot : LocalSlot :=
      .init (.aggregate 0 [.scalar ⟨bits, (itOf d).size.bytes⟩, .scalar ⟨b, 1⟩])
    have hset := localAllocsFrom_set ctx 0 body.localDecls locals i d newSlot hd
    simp only [Nat.zero_add, declSlotData_of_some htup, newSlot, tupleSlotData] at hset
    refine ⟨withMem m1 (ctx.base ++ localAllocs ctx body.localDecls (locals.set i newSlot))
        ⟨.Store, .None, ctx.addrs.getD i 0, ⟨(itOf d).size.bytes + (itOf d).size.bytes⟩⟩, ?_, ?_⟩
    · have hst' := hst
      simp only [localAllocs] at hst'
      rw [hset] at hst'
      rw [htyd] at hplace
      simp [evalStatement, hplace, hm1, placeStore, hst', localAllocs, newSlot]
    · refine ⟨h.hf, withMem_shape h1.shape _, by simp [h.nlocals], ?_, h.addrs⟩
      intro j d' slot' hd' hs'
      by_cases hij : i = j
      · subst hij
        rw [hd] at hd'; cases hd'
        simp [List.getElem?_set_self (by rw [h.nlocals]; exact hi)] at hs'
        subst hs'
        exact ⟨itOf d, by rw [htyd, tupleIntOfTy_intBoolTupleTy], rfl, hbits, rfl, hb⟩
      · rw [List.getElem?_set_ne hij] at hs'
        exact h.slots j d' slot' hd' hs'
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
    (hrest : ∀ e ∈ rest, e.1 ≠ localName i) {T : Gen.Type} {it : Gen.IntType} (hT : LocalTy T it)
    (hty : mapGet fr.func.locals (localName i) = some T) (L' : List Gen.Allocation)
    (hmem : cm.memory.allocations = ctx.base ++ L') (a : Gen.Allocation) (ha : L'[i]? = some a)
    (hlive : a.live = true) (haddr : a.addr = ctx.addrs.getD i 0) (hkind : a.kind = .Stack)
    (hlen : a.data.length = tyBytes T) (halign : a.align = ⟨it.size.bytes⟩) :
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
      LocalTy T it ∧ L'[i]? = some a ∧ a.live = true ∧ a.addr = ctx.addrs.getD i 0 ∧
      a.kind = .Stack ∧ a.data.length = tyBytes T ∧ a.align = ⟨it.size.bytes⟩) :
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
  have hck : checkValue (.Int v) (.Int it) = .ok () := checkValue_int hv
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

theorem typedStore_base_byte {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (p : Ptr) (r : Nat) (a : Gen.Allocation)
    (hp : p.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a) (hlive : a.live = true)
    (haddr : a.addr = p.addr) (hlen : a.data.length = u8Ty.size.bytes) (T : Gen.Type) (v : Val)
    (bits : Nat) (hck : checkValue v T = .ok ())
    (henc : Type.encode T v = .ok (scalarBytes u8Ty bits))
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    typedStore m p v T align .None =
      .ok (withMem m (ctx.base.set r { a with data := scalarBytes u8Ty bits } ++ L)
            ⟨.Store, .None, p.addr, u8Ty.size⟩) := by
  obtain ⟨hri, hai⟩ := List.getElem?_eq_some_iff.mp hr
  have hu8 : u8Ty.size.bytes = 1 := rfl
  have hblen : (scalarBytes u8Ty bits).length = u8Ty.size.bytes := by
    simp [scalarBytes, leBytes_length]
  have hne : scalarBytes u8Ty bits ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hblen, hu8]; omega)
  have hdrop : a.data.drop u8Ty.size.bytes = [] := List.drop_eq_nil_of_le (by omega)
  have hrlt : r < ctx.base.length + L.length := by omega
  simp only [typedStore, hck, henc, CM.store, BM.store, hal, BM.check_ptr, hp,
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
  | ordering =>
    exact typedStore_base_byte h p r a hp hr hlive haddr hlen orderingTy _ bits
      (checkValue_ordering hb) (encode_ordering hb) align hal

theorem typedStore_base_tuple {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (p : Ptr) (r : Nat) (a : Gen.Allocation)
    (hp : p.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a) (hlive : a.live = true)
    (haddr : a.addr = p.addr) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (hlen : a.data.length = it.size.bytes + it.size.bytes) (bits b : Nat)
    (hbits : bits < 2 ^ (8 * it.size.bytes)) (hb : b < 2)
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    typedStore m p (tupleVal it bits b) (intBoolTupleTy it) align .None =
      .ok (withMem m (ctx.base.set r { a with data := tupleBytes it bits b } ++ L)
            ⟨.Store, .None, p.addr, ⟨it.size.bytes + it.size.bytes⟩⟩) := by
  have hpos := hgood.pos
  obtain ⟨hri, hai⟩ := List.getElem?_eq_some_iff.mp hr
  have hblen := tupleBytes_length it bits b hpos
  have hck := checkValue_tuple it bits b hgood hbits
  have henc := encode_tuple it bits b hgood hbits hb
  have hne : tupleBytes it bits b ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hdrop : a.data.drop (it.size.bytes + it.size.bytes) = [] := List.drop_eq_nil_of_le (by omega)
  have hrlt : r < ctx.base.length + L.length := by omega
  simp only [typedStore, hck, henc, CM.store, BM.store, hal, BM.check_ptr, hp,
    listIndex, h.allocs]
  simp [hne, hlive, haddr, Allocation.size, hlen, hblen, writeSubsliceAtIndex, listSet, withMem,
    hdrop, List.set_append_left _ _ hri, hri, hrlt, hai]

theorem typedStore_base_localTy {m : Mach} {ctx : Ctx} {frames : List Frame} {L : List Gen.Allocation}
    (h : Shape m ctx frames (ctx.base ++ L)) (p : Ptr) (r : Nat) (a : Gen.Allocation)
    (hp : p.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a) (hlive : a.live = true)
    (haddr : a.addr = p.addr) (d : LocalDecl) (hd : scalarTypeOf d.ty = some (tyOf d))
    (hlen : a.data.length = tyBytes (tyOf d)) (v : Value) (hv : SlotOk (tyOf d) (.init v))
    (align : Align) (hal : Align.is_aligned align p.addr = true) :
    ∃ acc, typedStore m p (valOfValue (tyOf d) v) (tyOf d) align .None =
      .ok (withMem m (ctx.base.set r { a with data := declSlotData d (.init v) } ++ L) acc) := by
  rcases scalarTypeOf_cases hd with ⟨hb, _⟩ | ⟨it, hit, _⟩ | ⟨ho, _⟩ | ⟨it, ht, _⟩
  · obtain ⟨h1, h2⟩ := tyOf_bool hb
    have hfrag : FragTy (tyOf d) (itOf d) := by rw [h1, h2]; exact .bool
    rw [hfrag.declSlotData]
    rw [hfrag.tyBytes] at hlen
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      exact ⟨_, typedStore_base_frag h p r a hp hr hlive haddr hfrag hlen sc.bits hvb align hal⟩
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨_, htyT, _⟩ =>
      rw [h1] at htyT; simp at htyT
  · obtain ⟨h1, h2⟩ := tyOf_int hit
    have hfrag : FragTy (tyOf d) (itOf d) := by rw [h1, h2]; exact .int it (intTypeOf_good hit)
    rw [hfrag.declSlotData]
    rw [hfrag.tyBytes] at hlen
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      exact ⟨_, typedStore_base_frag h p r a hp hr hlive haddr hfrag hlen sc.bits hvb align hal⟩
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨_, htyT, _⟩ =>
      rw [h1] at htyT; simp at htyT
  · obtain ⟨h1, h2⟩ := tyOf_ordering ho
    have hfrag : FragTy (tyOf d) (itOf d) := by rw [h1, h2]; exact .ordering
    rw [hfrag.declSlotData]
    rw [hfrag.tyBytes] at hlen
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      exact ⟨_, typedStore_base_frag h p r a hp hr hlive haddr hfrag hlen sc.bits hvb align hal⟩
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨_, htyT, _⟩ =>
      rw [h1] at htyT; simp at htyT
  · obtain ⟨h1, h2⟩ := tyOf_tuple ht
    rw [declSlotData_of_some ht]
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ =>
      rw [h1] at hvb; simp [intBoolTupleTy, ValidBits] at hvb
    | .aggregate 0 [.scalar sc0, .scalar sc1], ⟨it', htyT, _, hb0, _, hb1⟩ =>
      rw [h1, tupleIntOfTy_intBoolTupleTy, Option.some.injEq] at htyT
      subst htyT
      have hlen' : a.data.length = it.size.bytes + it.size.bytes := by
        rw [h1] at hlen; exact hlen
      refine ⟨⟨.Store, .None, p.addr, ⟨it.size.bytes + it.size.bytes⟩⟩, ?_⟩
      rw [h1]
      simpa [valOfValue, tupleIntOfTy_intBoolTupleTy, tupleSlotData] using
        typedStore_base_tuple h p r a hp hr hlive haddr it (intBoolTupleOf_good ht) hlen'
          sc0.bits sc1.bits hb0 hb1 align hal

end MiniRustSpec.Correspondence
